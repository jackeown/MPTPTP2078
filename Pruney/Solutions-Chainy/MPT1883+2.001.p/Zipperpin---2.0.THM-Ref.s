%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I8T0FyeaX9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 187 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  374 (2477 expanded)
%              Number of equality atoms :   12 (  96 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t51_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v3_tex_2 @ C @ A )
                <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( v3_tex_2 @ C @ A )
                  <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_tex_2])).

thf('0',plain,
    ( ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_tex_2 @ sk_B @ sk_A )
   <= ~ ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v4_tex_2 @ sk_B @ sk_A )
   <= ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v4_tex_2 @ X0 @ X1 )
      | ( X2
       != ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( v4_tex_2 @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v4_tex_2 @ sk_B @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v4_tex_2 @ sk_B @ X0 )
      | ( v3_tex_2 @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v3_tex_2 @ sk_C_1 @ sk_A )
   <= ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,
    ( ~ ( v3_tex_2 @ sk_C_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( v3_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ( v4_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = sk_C_1 )
    | ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('32',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = sk_C_1 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v3_tex_2 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( v4_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('34',plain,
    ( ~ ( v3_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v3_tex_2 @ sk_C_1 @ sk_A )
   <= ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( v3_tex_2 @ sk_C_1 @ sk_A )
    | ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    v3_tex_2 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','20','36'])).

thf('38',plain,(
    v3_tex_2 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['22','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I8T0FyeaX9
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 23 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.21/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.46  thf(t51_tex_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.46                 ( ( v3_tex_2 @ C @ A ) <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46              ( ![C:$i]:
% 0.21/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46                  ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.46                    ( ( v3_tex_2 @ C @ A ) <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t51_tex_2])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((~ (v4_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((~ (v4_tex_2 @ sk_B @ sk_A)) <= (~ ((v4_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (~ ((v4_tex_2 @ sk_B @ sk_A)) | ~ ((v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('3', plain, (((v4_tex_2 @ sk_B @ sk_A) | (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain, (((v4_tex_2 @ sk_B @ sk_A)) <= (((v4_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain, (((sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d8_tex_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46           ( ( v4_tex_2 @ B @ A ) <=>
% 0.21/0.46             ( ![C:$i]:
% 0.21/0.46               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.46          | ~ (v4_tex_2 @ X0 @ X1)
% 0.21/0.46          | ((X2) != (u1_struct_0 @ X0))
% 0.21/0.46          | (v3_tex_2 @ X2 @ X1)
% 0.21/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.46          | ~ (l1_pre_topc @ X1)
% 0.21/0.46          | (v2_struct_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((v2_struct_0 @ X1)
% 0.21/0.46          | ~ (l1_pre_topc @ X1)
% 0.21/0.46          | ~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.46               (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.46          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X1)
% 0.21/0.46          | ~ (v4_tex_2 @ X0 @ X1)
% 0.21/0.46          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.46          | ~ (v4_tex_2 @ sk_B @ X0)
% 0.21/0.46          | (v3_tex_2 @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.46          | ~ (l1_pre_topc @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.46  thf('10', plain, (((sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.46          | ~ (v4_tex_2 @ sk_B @ X0)
% 0.21/0.46          | (v3_tex_2 @ sk_C_1 @ X0)
% 0.21/0.46          | ~ (l1_pre_topc @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (((v2_struct_0 @ sk_A)
% 0.21/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | (v3_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.46        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.21/0.46        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '11'])).
% 0.21/0.46  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (((v2_struct_0 @ sk_A)
% 0.21/0.46        | (v3_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.46        | ~ (v4_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.46  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain, ((~ (v4_tex_2 @ sk_B @ sk_A) | (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.46      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (((v3_tex_2 @ sk_C_1 @ sk_A)) <= (((v4_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      ((~ (v3_tex_2 @ sk_C_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_C_1 @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (((v3_tex_2 @ sk_C_1 @ sk_A)) | ~ ((v4_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain, (~ ((v4_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['2', '20'])).
% 0.21/0.46  thf('22', plain, (~ (v4_tex_2 @ sk_B @ sk_A)),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.21/0.46  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.46          | ((sk_C @ X0 @ X1) = (u1_struct_0 @ X0))
% 0.21/0.46          | (v4_tex_2 @ X0 @ X1)
% 0.21/0.46          | ~ (l1_pre_topc @ X1)
% 0.21/0.46          | (v2_struct_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (((v2_struct_0 @ sk_A)
% 0.21/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | (v4_tex_2 @ sk_B @ sk_A)
% 0.21/0.46        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain, (((sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (((v2_struct_0 @ sk_A)
% 0.21/0.46        | (v4_tex_2 @ sk_B @ sk_A)
% 0.21/0.46        | ((sk_C @ sk_B @ sk_A) = (sk_C_1)))),
% 0.21/0.46      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.46  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      ((((sk_C @ sk_B @ sk_A) = (sk_C_1)) | (v4_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.46  thf('31', plain, (~ (v4_tex_2 @ sk_B @ sk_A)),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.21/0.46  thf('32', plain, (((sk_C @ sk_B @ sk_A) = (sk_C_1))),
% 0.21/0.46      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.46          | ~ (v3_tex_2 @ (sk_C @ X0 @ X1) @ X1)
% 0.21/0.46          | (v4_tex_2 @ X0 @ X1)
% 0.21/0.46          | ~ (l1_pre_topc @ X1)
% 0.21/0.46          | (v2_struct_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      ((~ (v3_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.46        | (v2_struct_0 @ sk_A)
% 0.21/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | (v4_tex_2 @ sk_B @ sk_A)
% 0.21/0.46        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      (((v3_tex_2 @ sk_C_1 @ sk_A)) <= (((v3_tex_2 @ sk_C_1 @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('36', plain, (((v3_tex_2 @ sk_C_1 @ sk_A)) | ((v4_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('37', plain, (((v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['2', '20', '36'])).
% 0.21/0.46  thf('38', plain, ((v3_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.21/0.46  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('41', plain, (((v2_struct_0 @ sk_A) | (v4_tex_2 @ sk_B @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['34', '38', '39', '40'])).
% 0.21/0.46  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('43', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.21/0.46      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.46  thf('44', plain, ($false), inference('demod', [status(thm)], ['22', '43'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
