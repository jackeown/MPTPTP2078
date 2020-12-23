%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GeXfaSO6Es

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 ( 526 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tdlat_3 @ X10 )
      | ( v2_tex_2 @ X9 @ X10 )
      | ( X9
       != ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X10 ) @ X10 )
      | ~ ( v1_tdlat_3 @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X10 ) @ X10 )
      | ~ ( v1_tdlat_3 @ X10 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ( v2_tex_2 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','19','20'])).

thf('22',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GeXfaSO6Es
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 23 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.46  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.46  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.46  thf(t43_tex_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.46         ( l1_pre_topc @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.46            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.21/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t27_tex_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.21/0.46             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.46          | ~ (v1_tdlat_3 @ X10)
% 0.21/0.46          | (v2_tex_2 @ X9 @ X10)
% 0.21/0.46          | ((X9) != (u1_struct_0 @ X10))
% 0.21/0.46          | ~ (l1_pre_topc @ X10)
% 0.21/0.46          | (v2_struct_0 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X10 : $i]:
% 0.21/0.46         ((v2_struct_0 @ X10)
% 0.21/0.46          | ~ (l1_pre_topc @ X10)
% 0.21/0.46          | (v2_tex_2 @ (u1_struct_0 @ X10) @ X10)
% 0.21/0.46          | ~ (v1_tdlat_3 @ X10)
% 0.21/0.46          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.21/0.46               (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.46  thf(dt_k2_subset_1, axiom,
% 0.21/0.46    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.46  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.46  thf('4', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.46  thf('5', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X10 : $i]:
% 0.21/0.46         ((v2_struct_0 @ X10)
% 0.21/0.46          | ~ (l1_pre_topc @ X10)
% 0.21/0.46          | (v2_tex_2 @ (u1_struct_0 @ X10) @ X10)
% 0.21/0.46          | ~ (v1_tdlat_3 @ X10))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(t28_tex_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.46                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.46          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.46          | ~ (r1_tarski @ X13 @ X11)
% 0.21/0.46          | (v2_tex_2 @ X13 @ X12)
% 0.21/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.46          | ~ (l1_pre_topc @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (l1_pre_topc @ X0)
% 0.21/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.46          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.46          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.46        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.46        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.46  thf(d3_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]:
% 0.21/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(l3_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.46          | (r2_hidden @ X6 @ X8)
% 0.21/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_tarski @ sk_B @ X0)
% 0.21/0.46          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]:
% 0.21/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.46        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.46  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['11', '19', '20'])).
% 0.21/0.46  thf('22', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('23', plain, (~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.21/0.46      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((~ (v1_tdlat_3 @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '23'])).
% 0.21/0.46  thf('25', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.46  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
