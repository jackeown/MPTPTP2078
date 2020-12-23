%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7BedpcfaIu

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 173 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  427 (2207 expanded)
%              Number of equality atoms :   26 ( 112 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t16_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
              = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tex_2])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( sk_C @ X4 @ X5 )
        = ( u1_struct_0 @ X4 ) )
      | ( v1_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( v1_subset_1 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('14',plain,
    ( ( v1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( v1_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('16',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','21'])).

thf('23',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ C ) )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( u1_struct_0 @ X1 )
       != ( u1_struct_0 @ X3 ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[t5_tsep_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('32',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7BedpcfaIu
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 95 iterations in 0.052s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(t2_tsep_1, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X0 : $i]: ((m1_pre_topc @ X0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.54  thf(t16_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.54           ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.54             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.54              ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.54                ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t16_tex_2])).
% 0.21/0.54  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d3_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.54          | ((sk_C @ X4 @ X5) = (u1_struct_0 @ X4))
% 0.21/0.54          | (v1_tex_2 @ X4 @ X5)
% 0.21/0.54          | ~ (l1_pre_topc @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.54        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.54          | (m1_subset_1 @ (sk_C @ X4 @ X5) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.54          | (v1_tex_2 @ X4 @ X5)
% 0.21/0.54          | ~ (l1_pre_topc @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(d7_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         (((X8) = (X7))
% 0.21/0.54          | (v1_subset_1 @ X8 @ X7)
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((v1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.54          | ~ (v1_subset_1 @ (sk_C @ X4 @ X5) @ (u1_struct_0 @ X5))
% 0.21/0.54          | (v1_tex_2 @ X4 @ X5)
% 0.21/0.54          | ~ (l1_pre_topc @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.54        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_tex_2 @ sk_B @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.54  thf('20', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('21', plain, (((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.54        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5', '21'])).
% 0.21/0.54  thf('23', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf(t5_tsep_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.54               ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) =>
% 0.21/0.54                 ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.54                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.54          | ((u1_struct_0 @ X1) != (u1_struct_0 @ X3))
% 0.21/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))
% 0.21/0.54              = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.21/0.54          | ~ (m1_pre_topc @ X3 @ X2)
% 0.21/0.54          | ~ (l1_pre_topc @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_tsep_1])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (l1_pre_topc @ X1)
% 0.21/0.54          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.21/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.54              = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (l1_pre_topc @ X1)
% 0.21/0.54          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.21/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.54              = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.54          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.54              = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.54         != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.54         != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 0.21/0.54  thf('34', plain, ((~ (l1_pre_topc @ sk_A) | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '33'])).
% 0.21/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain, (~ (m1_pre_topc @ sk_A @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain, (~ (l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '36'])).
% 0.21/0.54  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain, ($false), inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
