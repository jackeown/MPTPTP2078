%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F9f9fyKW87

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:59 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 139 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  527 (1411 expanded)
%              Number of equality atoms :   52 ( 124 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

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

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('4',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf(dt_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k9_setfam_1 @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_setfam_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_setfam_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( k9_setfam_1 @ X1 )
      = ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k9_setfam_1 @ X1 )
      = ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_setfam_1 @ X0 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( k9_setfam_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k9_setfam_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k9_setfam_1 @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k9_setfam_1 @ X1 )
      = ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k9_setfam_1 @ X1 )
      = ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( X1 = X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( g1_pre_topc @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_setfam_1 @ X0 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k9_setfam_1 @ X1 )
      = ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( k9_setfam_1 @ X1 )
      = ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['34'])).

thf('36',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( ( u1_pre_topc @ X6 )
       != ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_tdlat_3 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    inference(demod,[status(thm)],['21','22','23'])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ( u1_pre_topc @ sk_A )
 != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F9f9fyKW87
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.44  % Solved by: fo/fo7.sh
% 0.18/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.44  % done 50 iterations in 0.016s
% 0.18/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.44  % SZS output start Refutation
% 0.18/0.44  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.18/0.44  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.18/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.44  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.18/0.44  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.18/0.44  thf(d1_tdlat_3, axiom,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( ( l1_pre_topc @ A ) =>
% 0.18/0.44       ( ( v1_tdlat_3 @ A ) <=>
% 0.18/0.44         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.18/0.44  thf('0', plain,
% 0.18/0.44      (![X6 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X6)
% 0.18/0.44          | ((u1_pre_topc @ X6) = (k9_setfam_1 @ (u1_struct_0 @ X6)))
% 0.18/0.44          | ~ (l1_pre_topc @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.18/0.44  thf(t17_tex_2, conjecture,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( ( l1_pre_topc @ A ) =>
% 0.18/0.44       ( ![B:$i]:
% 0.18/0.44         ( ( l1_pre_topc @ B ) =>
% 0.18/0.44           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.18/0.44                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.18/0.44               ( v1_tdlat_3 @ A ) ) =>
% 0.18/0.44             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.18/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.44    (~( ![A:$i]:
% 0.18/0.44        ( ( l1_pre_topc @ A ) =>
% 0.18/0.44          ( ![B:$i]:
% 0.18/0.44            ( ( l1_pre_topc @ B ) =>
% 0.18/0.44              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.18/0.44                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.18/0.44                  ( v1_tdlat_3 @ A ) ) =>
% 0.18/0.44                ( v1_tdlat_3 @ B ) ) ) ) ) )),
% 0.18/0.44    inference('cnf.neg', [status(esa)], [t17_tex_2])).
% 0.18/0.44  thf('1', plain,
% 0.18/0.44      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.18/0.44         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('2', plain,
% 0.18/0.44      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.18/0.44         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('3', plain,
% 0.18/0.44      (![X6 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X6)
% 0.18/0.44          | ((u1_pre_topc @ X6) = (k9_setfam_1 @ (u1_struct_0 @ X6)))
% 0.18/0.44          | ~ (l1_pre_topc @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.18/0.44  thf('4', plain,
% 0.18/0.44      (![X6 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X6)
% 0.18/0.44          | ((u1_pre_topc @ X6) = (k9_setfam_1 @ (u1_struct_0 @ X6)))
% 0.18/0.44          | ~ (l1_pre_topc @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.18/0.44  thf(dt_k9_setfam_1, axiom,
% 0.18/0.44    (![A:$i]:
% 0.18/0.44     ( m1_subset_1 @
% 0.18/0.44       ( k9_setfam_1 @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.18/0.44  thf('5', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (m1_subset_1 @ (k9_setfam_1 @ X0) @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.18/0.44      inference('cnf', [status(esa)], [dt_k9_setfam_1])).
% 0.18/0.44  thf(redefinition_k9_setfam_1, axiom,
% 0.18/0.44    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.18/0.44  thf('6', plain, (![X1 : $i]: ((k9_setfam_1 @ X1) = (k1_zfmisc_1 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.18/0.44  thf('7', plain, (![X1 : $i]: ((k9_setfam_1 @ X1) = (k1_zfmisc_1 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.18/0.44  thf('8', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (m1_subset_1 @ (k9_setfam_1 @ X0) @ (k9_setfam_1 @ (k9_setfam_1 @ X0)))),
% 0.18/0.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.18/0.44  thf('9', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         ((m1_subset_1 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ 
% 0.18/0.44           (k9_setfam_1 @ (u1_pre_topc @ X0)))
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0))),
% 0.18/0.44      inference('sup+', [status(thm)], ['4', '8'])).
% 0.18/0.44  thf('10', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.18/0.44           (k9_setfam_1 @ (u1_pre_topc @ X0)))
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ~ (l1_pre_topc @ X0))),
% 0.18/0.44      inference('sup+', [status(thm)], ['3', '9'])).
% 0.18/0.44  thf('11', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.18/0.44             (k9_setfam_1 @ (u1_pre_topc @ X0))))),
% 0.18/0.44      inference('simplify', [status(thm)], ['10'])).
% 0.18/0.44  thf('12', plain,
% 0.18/0.44      (![X6 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X6)
% 0.18/0.44          | ((u1_pre_topc @ X6) = (k9_setfam_1 @ (u1_struct_0 @ X6)))
% 0.18/0.44          | ~ (l1_pre_topc @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.18/0.44  thf(free_g1_pre_topc, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.44       ( ![C:$i,D:$i]:
% 0.18/0.44         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.18/0.44           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.18/0.44  thf('13', plain,
% 0.18/0.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.44         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.18/0.44          | ((X5) = (X3))
% 0.18/0.44          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.18/0.44      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.18/0.44  thf('14', plain, (![X1 : $i]: ((k9_setfam_1 @ X1) = (k1_zfmisc_1 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.18/0.44  thf('15', plain, (![X1 : $i]: ((k9_setfam_1 @ X1) = (k1_zfmisc_1 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.18/0.44  thf('16', plain,
% 0.18/0.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.44         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.18/0.44          | ((X5) = (X3))
% 0.18/0.44          | ~ (m1_subset_1 @ X5 @ (k9_setfam_1 @ (k9_setfam_1 @ X4))))),
% 0.18/0.44      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.18/0.44  thf('17', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.44         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ (u1_pre_topc @ X0)))
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ((X1) = (X2))
% 0.18/0.44          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ X1) != (g1_pre_topc @ X3 @ X2)))),
% 0.18/0.44      inference('sup-', [status(thm)], ['12', '16'])).
% 0.18/0.44  thf('18', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.44         (~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.18/0.44              != (g1_pre_topc @ X2 @ X1))
% 0.18/0.44          | ((u1_pre_topc @ X0) = (X1))
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ~ (l1_pre_topc @ X0))),
% 0.18/0.44      inference('sup-', [status(thm)], ['11', '17'])).
% 0.18/0.44  thf('19', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.44         (((u1_pre_topc @ X0) = (X1))
% 0.18/0.44          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.18/0.44              != (g1_pre_topc @ X2 @ X1))
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ~ (l1_pre_topc @ X0))),
% 0.18/0.44      inference('simplify', [status(thm)], ['18'])).
% 0.18/0.44  thf('20', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.18/0.44            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ((u1_pre_topc @ X0) = (u1_pre_topc @ sk_B)))),
% 0.18/0.44      inference('sup-', [status(thm)], ['2', '19'])).
% 0.18/0.44  thf('21', plain,
% 0.18/0.44      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))
% 0.18/0.44        | ~ (v1_tdlat_3 @ sk_A)
% 0.18/0.44        | ~ (l1_pre_topc @ sk_A))),
% 0.18/0.44      inference('eq_res', [status(thm)], ['20'])).
% 0.18/0.44  thf('22', plain, ((v1_tdlat_3 @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('24', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.18/0.44      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.18/0.44  thf('25', plain,
% 0.18/0.44      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.18/0.44         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.18/0.44      inference('demod', [status(thm)], ['1', '24'])).
% 0.18/0.44  thf('26', plain,
% 0.18/0.44      (![X6 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X6)
% 0.18/0.44          | ((u1_pre_topc @ X6) = (k9_setfam_1 @ (u1_struct_0 @ X6)))
% 0.18/0.44          | ~ (l1_pre_topc @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.18/0.44  thf('27', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (m1_subset_1 @ (k9_setfam_1 @ X0) @ (k9_setfam_1 @ (k9_setfam_1 @ X0)))),
% 0.18/0.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.18/0.44  thf('28', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.18/0.44           (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X0))))
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0))),
% 0.18/0.44      inference('sup+', [status(thm)], ['26', '27'])).
% 0.18/0.44  thf('29', plain,
% 0.18/0.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.44         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.18/0.44          | ((X4) = (X2))
% 0.18/0.44          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.18/0.44      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.18/0.44  thf('30', plain, (![X1 : $i]: ((k9_setfam_1 @ X1) = (k1_zfmisc_1 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.18/0.44  thf('31', plain, (![X1 : $i]: ((k9_setfam_1 @ X1) = (k1_zfmisc_1 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.18/0.44  thf('32', plain,
% 0.18/0.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.44         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.18/0.44          | ((X4) = (X2))
% 0.18/0.44          | ~ (m1_subset_1 @ X5 @ (k9_setfam_1 @ (k9_setfam_1 @ X4))))),
% 0.18/0.44      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.18/0.44  thf('33', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.44         (~ (v1_tdlat_3 @ X0)
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ((u1_struct_0 @ X0) = (X1))
% 0.18/0.44          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.18/0.44              != (g1_pre_topc @ X1 @ X2)))),
% 0.18/0.44      inference('sup-', [status(thm)], ['28', '32'])).
% 0.18/0.44  thf('34', plain,
% 0.18/0.44      (![X0 : $i]:
% 0.18/0.44         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.18/0.44            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.18/0.44          | ((u1_struct_0 @ X0) = (u1_struct_0 @ sk_B))
% 0.18/0.44          | ~ (l1_pre_topc @ X0)
% 0.18/0.44          | ~ (v1_tdlat_3 @ X0))),
% 0.18/0.44      inference('sup-', [status(thm)], ['25', '33'])).
% 0.18/0.44  thf('35', plain,
% 0.18/0.44      ((~ (v1_tdlat_3 @ sk_A)
% 0.18/0.44        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.44        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.18/0.44      inference('eq_res', [status(thm)], ['34'])).
% 0.18/0.44  thf('36', plain, ((v1_tdlat_3 @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('38', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.18/0.44      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.18/0.44  thf('39', plain,
% 0.18/0.44      (![X6 : $i]:
% 0.18/0.44         (((u1_pre_topc @ X6) != (k9_setfam_1 @ (u1_struct_0 @ X6)))
% 0.18/0.44          | (v1_tdlat_3 @ X6)
% 0.18/0.44          | ~ (l1_pre_topc @ X6))),
% 0.18/0.44      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.18/0.44  thf('40', plain,
% 0.18/0.44      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.44        | ~ (l1_pre_topc @ sk_B)
% 0.18/0.44        | (v1_tdlat_3 @ sk_B))),
% 0.18/0.44      inference('sup-', [status(thm)], ['38', '39'])).
% 0.18/0.44  thf('41', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B))),
% 0.18/0.44      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.18/0.44  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('43', plain,
% 0.18/0.44      ((((u1_pre_topc @ sk_A) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.44        | (v1_tdlat_3 @ sk_B))),
% 0.18/0.44      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.18/0.44  thf('44', plain, (~ (v1_tdlat_3 @ sk_B)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('45', plain,
% 0.18/0.44      (((u1_pre_topc @ sk_A) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.44      inference('clc', [status(thm)], ['43', '44'])).
% 0.18/0.44  thf('46', plain,
% 0.18/0.44      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.18/0.44        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.44        | ~ (v1_tdlat_3 @ sk_A))),
% 0.18/0.44      inference('sup-', [status(thm)], ['0', '45'])).
% 0.18/0.44  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('48', plain, ((v1_tdlat_3 @ sk_A)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('49', plain, (((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))),
% 0.18/0.44      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.18/0.44  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.18/0.44  
% 0.18/0.44  % SZS output end Refutation
% 0.18/0.44  
% 0.18/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
