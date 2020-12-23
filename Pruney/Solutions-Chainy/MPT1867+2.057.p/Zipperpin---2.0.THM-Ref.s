%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LeL2lr9CKI

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:33 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  429 ( 732 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22','25'])).

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
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','29','41'])).

thf('43',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LeL2lr9CKI
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:32:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.07  % Solved by: fo/fo7.sh
% 0.91/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.07  % done 1273 iterations in 0.617s
% 0.91/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.07  % SZS output start Refutation
% 0.91/1.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.07  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.91/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.91/1.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.07  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.91/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.07  thf(t35_tex_2, conjecture,
% 0.91/1.07    (![A:$i]:
% 0.91/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.07       ( ![B:$i]:
% 0.91/1.07         ( ( ( v1_xboole_0 @ B ) & 
% 0.91/1.07             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.07           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.91/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.07    (~( ![A:$i]:
% 0.91/1.07        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.07            ( l1_pre_topc @ A ) ) =>
% 0.91/1.07          ( ![B:$i]:
% 0.91/1.07            ( ( ( v1_xboole_0 @ B ) & 
% 0.91/1.07                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.07              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.91/1.07    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.91/1.07  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf(l13_xboole_0, axiom,
% 0.91/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.07  thf('2', plain,
% 0.91/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.07  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.07  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.91/1.07      inference('demod', [status(thm)], ['0', '3'])).
% 0.91/1.07  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('6', plain,
% 0.91/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.07  thf(t4_subset_1, axiom,
% 0.91/1.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.07  thf('7', plain,
% 0.91/1.07      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.91/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.07  thf('8', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i]:
% 0.91/1.07         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.07      inference('sup+', [status(thm)], ['6', '7'])).
% 0.91/1.07  thf(cc2_pre_topc, axiom,
% 0.91/1.07    (![A:$i]:
% 0.91/1.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.07       ( ![B:$i]:
% 0.91/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.07           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.91/1.07  thf('9', plain,
% 0.91/1.07      (![X15 : $i, X16 : $i]:
% 0.91/1.07         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.07          | (v4_pre_topc @ X15 @ X16)
% 0.91/1.07          | ~ (v1_xboole_0 @ X15)
% 0.91/1.07          | ~ (l1_pre_topc @ X16)
% 0.91/1.07          | ~ (v2_pre_topc @ X16))),
% 0.91/1.07      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.91/1.07  thf('10', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i]:
% 0.91/1.07         (~ (v1_xboole_0 @ X1)
% 0.91/1.07          | ~ (v2_pre_topc @ X0)
% 0.91/1.07          | ~ (l1_pre_topc @ X0)
% 0.91/1.07          | ~ (v1_xboole_0 @ X1)
% 0.91/1.07          | (v4_pre_topc @ X1 @ X0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.07  thf('11', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i]:
% 0.91/1.07         ((v4_pre_topc @ X1 @ X0)
% 0.91/1.07          | ~ (l1_pre_topc @ X0)
% 0.91/1.07          | ~ (v2_pre_topc @ X0)
% 0.91/1.07          | ~ (v1_xboole_0 @ X1))),
% 0.91/1.07      inference('simplify', [status(thm)], ['10'])).
% 0.91/1.07  thf('12', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         (~ (v1_xboole_0 @ X0)
% 0.91/1.07          | ~ (v2_pre_topc @ sk_A)
% 0.91/1.07          | (v4_pre_topc @ X0 @ sk_A))),
% 0.91/1.07      inference('sup-', [status(thm)], ['5', '11'])).
% 0.91/1.07  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('14', plain,
% 0.91/1.07      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.91/1.07      inference('demod', [status(thm)], ['12', '13'])).
% 0.91/1.07  thf('15', plain,
% 0.91/1.07      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.91/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.07  thf('16', plain,
% 0.91/1.07      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.91/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.07  thf(d6_tex_2, axiom,
% 0.91/1.07    (![A:$i]:
% 0.91/1.07     ( ( l1_pre_topc @ A ) =>
% 0.91/1.07       ( ![B:$i]:
% 0.91/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.07           ( ( v2_tex_2 @ B @ A ) <=>
% 0.91/1.07             ( ![C:$i]:
% 0.91/1.07               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.07                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.91/1.07                      ( ![D:$i]:
% 0.91/1.07                        ( ( m1_subset_1 @
% 0.91/1.07                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.07                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.91/1.07                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.91/1.07                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.07  thf('17', plain,
% 0.91/1.07      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.91/1.07         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.91/1.07          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.91/1.07          | ~ (v4_pre_topc @ X20 @ X18)
% 0.91/1.07          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.91/1.07              != (sk_C @ X17 @ X18))
% 0.91/1.07          | (v2_tex_2 @ X17 @ X18)
% 0.91/1.07          | ~ (l1_pre_topc @ X18))),
% 0.91/1.07      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.91/1.07  thf('18', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i]:
% 0.91/1.07         (~ (l1_pre_topc @ X0)
% 0.91/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.07          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.91/1.07              != (sk_C @ k1_xboole_0 @ X0))
% 0.91/1.07          | ~ (v4_pre_topc @ X1 @ X0)
% 0.91/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.91/1.07      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.07  thf('19', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.91/1.07          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.91/1.07              != (sk_C @ k1_xboole_0 @ X0))
% 0.91/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.07          | ~ (l1_pre_topc @ X0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['15', '18'])).
% 0.91/1.07  thf('20', plain,
% 0.91/1.07      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.91/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.07  thf(redefinition_k9_subset_1, axiom,
% 0.91/1.07    (![A:$i,B:$i,C:$i]:
% 0.91/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.07       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.91/1.07  thf('21', plain,
% 0.91/1.07      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.07         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.91/1.07          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.07      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.91/1.07  thf('22', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i]:
% 0.91/1.07         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.91/1.07           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.91/1.07  thf('23', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.91/1.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.07  thf(t28_xboole_1, axiom,
% 0.91/1.07    (![A:$i,B:$i]:
% 0.91/1.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.07  thf('24', plain,
% 0.91/1.07      (![X1 : $i, X2 : $i]:
% 0.91/1.07         (((k3_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_tarski @ X1 @ X2))),
% 0.91/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.07  thf('25', plain,
% 0.91/1.07      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.07  thf('26', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.91/1.07          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.91/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.07          | ~ (l1_pre_topc @ X0))),
% 0.91/1.07      inference('demod', [status(thm)], ['19', '22', '25'])).
% 0.91/1.07  thf('27', plain,
% 0.91/1.07      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.07        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.91/1.07        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.91/1.07      inference('sup-', [status(thm)], ['14', '26'])).
% 0.91/1.07  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.07  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.07  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('30', plain,
% 0.91/1.07      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.91/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.07  thf('31', plain,
% 0.91/1.07      (![X17 : $i, X18 : $i]:
% 0.91/1.07         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.91/1.07          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.91/1.07          | (v2_tex_2 @ X17 @ X18)
% 0.91/1.07          | ~ (l1_pre_topc @ X18))),
% 0.91/1.07      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.91/1.07  thf('32', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         (~ (l1_pre_topc @ X0)
% 0.91/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.07          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.07  thf(t3_xboole_1, axiom,
% 0.91/1.07    (![A:$i]:
% 0.91/1.07     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.07  thf('33', plain,
% 0.91/1.07      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.91/1.07      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.07  thf('34', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.07          | ~ (l1_pre_topc @ X0)
% 0.91/1.07          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.91/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.91/1.07  thf('35', plain,
% 0.91/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.07  thf('36', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.91/1.07      inference('demod', [status(thm)], ['0', '3'])).
% 0.91/1.07  thf('37', plain,
% 0.91/1.07      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.07  thf('38', plain,
% 0.91/1.07      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.91/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.07        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['34', '37'])).
% 0.91/1.07  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.07  thf('41', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.91/1.07      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.91/1.07  thf('42', plain,
% 0.91/1.07      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.91/1.07      inference('demod', [status(thm)], ['27', '28', '29', '41'])).
% 0.91/1.07  thf('43', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.91/1.07      inference('simplify', [status(thm)], ['42'])).
% 0.91/1.07  thf('44', plain, ($false), inference('demod', [status(thm)], ['4', '43'])).
% 0.91/1.07  
% 0.91/1.07  % SZS output end Refutation
% 0.91/1.07  
% 0.91/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
