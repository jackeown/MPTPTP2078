%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q1fycROTiK

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 281 expanded)
%              Number of leaves         :   17 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          :  449 (2818 expanded)
%              Number of equality atoms :   52 ( 260 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t17_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v1_tdlat_3 @ A ) )
           => ( v1_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v1_tdlat_3 @ A ) )
             => ( v1_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tex_2])).

thf('0',plain,(
    ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v1_tdlat_3 @ X11 )
      | ( ( u1_pre_topc @ X11 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('3',plain,(
    ! [X11: $i] :
      ( ~ ( v1_tdlat_3 @ X11 )
      | ( ( u1_pre_topc @ X11 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k9_setfam_1 @ X6 )
      = ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k9_setfam_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_pre_topc @ X9 @ X10 )
       != ( g1_pre_topc @ X7 @ X8 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k9_setfam_1 @ X6 )
      = ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k9_setfam_1 @ X6 )
      = ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_pre_topc @ X9 @ X10 )
       != ( g1_pre_topc @ X7 @ X8 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_setfam_1 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ X0 @ ( k9_setfam_1 @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ X0 @ ( k9_setfam_1 @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( k9_setfam_1 @ X0 )
        = ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) )
        = ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,
    ( ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
      = ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','25'])).

thf('27',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('28',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('29',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_pre_topc @ X9 @ X10 )
       != ( g1_pre_topc @ X7 @ X8 ) )
      | ( X9 = X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k9_setfam_1 @ X6 )
      = ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( k9_setfam_1 @ X6 )
      = ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_pre_topc @ X9 @ X10 )
       != ( g1_pre_topc @ X7 @ X8 ) )
      | ( X9 = X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_pre_topc @ X0 @ ( k9_setfam_1 @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_A )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( ( u1_pre_topc @ X11 )
       != ( k9_setfam_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_tdlat_3 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('40',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('42',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q1fycROTiK
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 42 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.48  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.48  thf(t17_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_pre_topc @ B ) =>
% 0.21/0.48           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.49                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.49               ( v1_tdlat_3 @ A ) ) =>
% 0.21/0.49             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_pre_topc @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( l1_pre_topc @ B ) =>
% 0.21/0.49              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.49                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.49                  ( v1_tdlat_3 @ A ) ) =>
% 0.21/0.49                ( v1_tdlat_3 @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t17_tex_2])).
% 0.21/0.49  thf('0', plain, (~ (v1_tdlat_3 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_tdlat_3, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ( v1_tdlat_3 @ A ) <=>
% 0.21/0.49         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v1_tdlat_3 @ X11)
% 0.21/0.49          | ((u1_pre_topc @ X11) = (k9_setfam_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v1_tdlat_3 @ X11)
% 0.21/0.49          | ((u1_pre_topc @ X11) = (k9_setfam_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('8', plain, (![X6 : $i]: ((k9_setfam_1 @ X6) = (k1_zfmisc_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X3 @ (k9_setfam_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.49  thf(free_g1_pre_topc, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ![C:$i,D:$i]:
% 0.21/0.49         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.49           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((g1_pre_topc @ X9 @ X10) != (g1_pre_topc @ X7 @ X8))
% 0.21/0.49          | ((X10) = (X8))
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.49      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.49  thf('12', plain, (![X6 : $i]: ((k9_setfam_1 @ X6) = (k1_zfmisc_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('13', plain, (![X6 : $i]: ((k9_setfam_1 @ X6) = (k1_zfmisc_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((g1_pre_topc @ X9 @ X10) != (g1_pre_topc @ X7 @ X8))
% 0.21/0.49          | ((X10) = (X8))
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k9_setfam_1 @ (k9_setfam_1 @ X9))))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (((k9_setfam_1 @ X0) = (X1))
% 0.21/0.49          | ((g1_pre_topc @ X0 @ (k9_setfam_1 @ X0)) != (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((g1_pre_topc @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.49            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.49          | ((k9_setfam_1 @ X0) = (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.49            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.49          | ((k9_setfam_1 @ (u1_struct_0 @ X0)) = (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_B))
% 0.21/0.49        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('eq_res', [status(thm)], ['17'])).
% 0.21/0.49  thf('19', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '21'])).
% 0.21/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.49  thf('28', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((g1_pre_topc @ X9 @ X10) != (g1_pre_topc @ X7 @ X8))
% 0.21/0.49          | ((X9) = (X7))
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.49      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.49  thf('32', plain, (![X6 : $i]: ((k9_setfam_1 @ X6) = (k1_zfmisc_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('33', plain, (![X6 : $i]: ((k9_setfam_1 @ X6) = (k1_zfmisc_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((g1_pre_topc @ X9 @ X10) != (g1_pre_topc @ X7 @ X8))
% 0.21/0.49          | ((X9) = (X7))
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k9_setfam_1 @ (k9_setfam_1 @ X9))))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (((X0) = (X1))
% 0.21/0.49          | ((g1_pre_topc @ X0 @ (k9_setfam_1 @ X0)) != (g1_pre_topc @ X1 @ X2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.49          | ((u1_struct_0 @ sk_A) = (X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49          != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.49        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '36'])).
% 0.21/0.49  thf('38', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (((u1_pre_topc @ X11) != (k9_setfam_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | (v1_tdlat_3 @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (v1_tdlat_3 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A)) | (v1_tdlat_3 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.21/0.49  thf('45', plain, ((v1_tdlat_3 @ sk_B)),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
