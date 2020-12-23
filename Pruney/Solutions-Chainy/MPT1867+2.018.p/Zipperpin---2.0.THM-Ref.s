%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uvluvAKbPT

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:28 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 107 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  461 ( 803 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_2 ),
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
    sk_B_2 = k1_xboole_0 ),
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

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
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

thf('17',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X27 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X29 )
       != ( sk_C @ X26 @ X27 ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X12 @ X11 @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( sk_C @ X26 @ X27 ) @ X26 )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','29','44'])).

thf('46',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['4','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uvluvAKbPT
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:10:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 1634 iterations in 0.672s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.90/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.12  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.12  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.90/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.12  thf(t35_tex_2, conjecture,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( ( v1_xboole_0 @ B ) & 
% 0.90/1.12             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.12           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i]:
% 0.90/1.12        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.12            ( l1_pre_topc @ A ) ) =>
% 0.90/1.12          ( ![B:$i]:
% 0.90/1.12            ( ( ( v1_xboole_0 @ B ) & 
% 0.90/1.12                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.12              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.90/1.12  thf('0', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('1', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(l13_xboole_0, axiom,
% 0.90/1.12    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.12  thf('2', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('3', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.12  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.12      inference('demod', [status(thm)], ['0', '3'])).
% 0.90/1.12  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf(t4_subset_1, axiom,
% 0.90/1.12    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.12  thf('7', plain,
% 0.90/1.12      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.12  thf('8', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.12  thf(cc1_tops_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.90/1.12  thf('9', plain,
% 0.90/1.12      (![X24 : $i, X25 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.90/1.12          | (v3_pre_topc @ X24 @ X25)
% 0.90/1.12          | ~ (v1_xboole_0 @ X24)
% 0.90/1.12          | ~ (l1_pre_topc @ X25)
% 0.90/1.12          | ~ (v2_pre_topc @ X25))),
% 0.90/1.12      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.90/1.12  thf('10', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v1_xboole_0 @ X1)
% 0.90/1.12          | ~ (v2_pre_topc @ X0)
% 0.90/1.12          | ~ (l1_pre_topc @ X0)
% 0.90/1.12          | ~ (v1_xboole_0 @ X1)
% 0.90/1.12          | (v3_pre_topc @ X1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.12  thf('11', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((v3_pre_topc @ X1 @ X0)
% 0.90/1.12          | ~ (l1_pre_topc @ X0)
% 0.90/1.12          | ~ (v2_pre_topc @ X0)
% 0.90/1.12          | ~ (v1_xboole_0 @ X1))),
% 0.90/1.12      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.12  thf('12', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v1_xboole_0 @ X0)
% 0.90/1.12          | ~ (v2_pre_topc @ sk_A)
% 0.90/1.12          | (v3_pre_topc @ X0 @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '11'])).
% 0.90/1.12  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('14', plain,
% 0.90/1.12      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.90/1.12      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.12  thf('15', plain,
% 0.90/1.12      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.12  thf(d5_tex_2, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( l1_pre_topc @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12           ( ( v2_tex_2 @ B @ A ) <=>
% 0.90/1.12             ( ![C:$i]:
% 0.90/1.12               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.90/1.12                      ( ![D:$i]:
% 0.90/1.12                        ( ( m1_subset_1 @
% 0.90/1.12                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.90/1.12                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.90/1.12                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.12  thf('17', plain,
% 0.90/1.12      (![X26 : $i, X27 : $i, X29 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.90/1.12          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.90/1.12          | ~ (v3_pre_topc @ X29 @ X27)
% 0.90/1.12          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X26 @ X29)
% 0.90/1.12              != (sk_C @ X26 @ X27))
% 0.90/1.12          | (v2_tex_2 @ X26 @ X27)
% 0.90/1.12          | ~ (l1_pre_topc @ X27))),
% 0.90/1.12      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.90/1.12  thf('18', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (l1_pre_topc @ X0)
% 0.90/1.12          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.12          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.90/1.12              != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.12          | ~ (v3_pre_topc @ X1 @ X0)
% 0.90/1.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.12  thf('19', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.90/1.12          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.90/1.12              != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.12          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.12          | ~ (l1_pre_topc @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['15', '18'])).
% 0.90/1.12  thf(d10_xboole_0, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.12  thf('20', plain,
% 0.90/1.12      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.90/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.12  thf('21', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.90/1.12      inference('simplify', [status(thm)], ['20'])).
% 0.90/1.12  thf(t3_subset, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.12  thf('22', plain,
% 0.90/1.12      (![X15 : $i, X17 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.12  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.12  thf(idempotence_k9_subset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.12       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.90/1.12  thf('24', plain,
% 0.90/1.12      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.12         (((k9_subset_1 @ X12 @ X11 @ X11) = (X11))
% 0.90/1.12          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.90/1.12      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.90/1.12  thf('25', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.12  thf('26', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.90/1.12          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.12          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.12          | ~ (l1_pre_topc @ X0))),
% 0.90/1.12      inference('demod', [status(thm)], ['19', '25'])).
% 0.90/1.12  thf('27', plain,
% 0.90/1.12      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.12        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.12        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.90/1.12        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['14', '26'])).
% 0.90/1.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.12  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('30', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.12  thf('31', plain,
% 0.90/1.12      (![X26 : $i, X27 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.90/1.12          | (r1_tarski @ (sk_C @ X26 @ X27) @ X26)
% 0.90/1.12          | (v2_tex_2 @ X26 @ X27)
% 0.90/1.12          | ~ (l1_pre_topc @ X27))),
% 0.90/1.12      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.90/1.12  thf('32', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v1_xboole_0 @ X1)
% 0.90/1.12          | ~ (l1_pre_topc @ X0)
% 0.90/1.12          | (v2_tex_2 @ X1 @ X0)
% 0.90/1.12          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.12  thf('33', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.12  thf('34', plain,
% 0.90/1.12      (![X15 : $i, X16 : $i]:
% 0.90/1.12         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | (r1_tarski @ X1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.12  thf('36', plain,
% 0.90/1.12      (![X2 : $i, X4 : $i]:
% 0.90/1.12         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.90/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.12  thf('37', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.90/1.12  thf('38', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((v2_tex_2 @ X0 @ X1)
% 0.90/1.12          | ~ (l1_pre_topc @ X1)
% 0.90/1.12          | ~ (v1_xboole_0 @ X0)
% 0.90/1.12          | ((sk_C @ X0 @ X1) = (X0))
% 0.90/1.12          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['32', '37'])).
% 0.90/1.12  thf('39', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (((sk_C @ X0 @ X1) = (X0))
% 0.90/1.12          | ~ (v1_xboole_0 @ X0)
% 0.90/1.12          | ~ (l1_pre_topc @ X1)
% 0.90/1.12          | (v2_tex_2 @ X0 @ X1))),
% 0.90/1.12      inference('simplify', [status(thm)], ['38'])).
% 0.90/1.12  thf('40', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.12      inference('demod', [status(thm)], ['0', '3'])).
% 0.90/1.12  thf('41', plain,
% 0.90/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.12        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.12        | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.12  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf('44', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.90/1.12  thf('45', plain,
% 0.90/1.12      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.90/1.12      inference('demod', [status(thm)], ['27', '28', '29', '44'])).
% 0.90/1.12  thf('46', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.12      inference('simplify', [status(thm)], ['45'])).
% 0.90/1.12  thf('47', plain, ($false), inference('demod', [status(thm)], ['4', '46'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.90/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
