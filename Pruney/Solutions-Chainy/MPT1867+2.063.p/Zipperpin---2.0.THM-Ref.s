%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DIUcShmkP8

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 117 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  451 ( 909 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
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

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( sk_C @ X14 @ X15 ) @ X14 )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X15 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X17 )
       != ( sk_C @ X14 @ X15 ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('46',plain,(
    k1_xboole_0
 != ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DIUcShmkP8
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 179 iterations in 0.129s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(t4_subset_1, axiom,
% 0.20/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf(d6_tex_2, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.58             ( ![C:$i]:
% 0.20/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.20/0.58                      ( ![D:$i]:
% 0.20/0.58                        ( ( m1_subset_1 @
% 0.20/0.58                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.20/0.58                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.58                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.58          | (r1_tarski @ (sk_C @ X14 @ X15) @ X14)
% 0.20/0.58          | (v2_tex_2 @ X14 @ X15)
% 0.20/0.58          | ~ (l1_pre_topc @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X0)
% 0.20/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.58          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.58  thf(t12_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X1 : $i, X2 : $i]:
% 0.20/0.58         (((k2_xboole_0 @ X2 @ X1) = (X1)) | ~ (r1_tarski @ X2 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ((k2_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.58              = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf(t1_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.58  thf('5', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.58  thf(l13_xboole_0, axiom,
% 0.20/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf(t35_tex_2, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.58           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.58            ( l1_pre_topc @ A ) ) =>
% 0.20/0.58          ( ![B:$i]:
% 0.20/0.58            ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.58              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.20/0.58  thf('8', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('9', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.58  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('16', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.58  thf('19', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.20/0.58  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.58  thf(cc2_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.58           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.58          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.58          | ~ (v1_xboole_0 @ X12)
% 0.20/0.58          | ~ (l1_pre_topc @ X13)
% 0.20/0.58          | ~ (v2_pre_topc @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ X1)
% 0.20/0.58          | ~ (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (v1_xboole_0 @ X1)
% 0.20/0.58          | (v4_pre_topc @ X1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((v4_pre_topc @ X1 @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ X0)
% 0.20/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58          | (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.58  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.58          | ~ (v4_pre_topc @ X17 @ X15)
% 0.20/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ X14 @ X17)
% 0.20/0.58              != (sk_C @ X14 @ X15))
% 0.20/0.58          | (v2_tex_2 @ X14 @ X15)
% 0.20/0.58          | ~ (l1_pre_topc @ X15))),
% 0.20/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X0)
% 0.20/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.20/0.58              != (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.58          | ~ (v4_pre_topc @ X1 @ X0)
% 0.20/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.58              != (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.58         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.20/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.20/0.58           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf(t2_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.20/0.58        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['29', '40'])).
% 0.20/0.58  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.58  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (((v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.20/0.58        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.20/0.58      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.58  thf('45', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.58  thf('46', plain, (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))),
% 0.20/0.58      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain, ($false),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['19', '46'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
