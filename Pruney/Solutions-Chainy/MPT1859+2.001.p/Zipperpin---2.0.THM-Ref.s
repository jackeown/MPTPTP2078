%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lU3QhGttM0

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 115 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  472 (1285 expanded)
%              Number of equality atoms :   12 (  56 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t27_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( B
                = ( u1_struct_0 @ A ) )
             => ( ( v2_tex_2 @ B @ A )
              <=> ( v1_tdlat_3 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tex_2])).

thf('0',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('5',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X3
       != ( u1_struct_0 @ X1 ) )
      | ~ ( v2_tex_2 @ X3 @ X2 )
      | ( v1_tdlat_3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v1_tdlat_3 @ X1 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X1 ) @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ sk_A )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ sk_A )
      | ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf('18',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf('25',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
   <= ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('30',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X3
       != ( u1_struct_0 @ X1 ) )
      | ~ ( v1_tdlat_3 @ X1 )
      | ( v2_tex_2 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X1 ) @ X2 )
      | ~ ( v1_tdlat_3 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('39',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('48',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lU3QhGttM0
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:47:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 24 iterations in 0.014s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(t27_tex_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.21/0.47             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47              ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.21/0.47                ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t27_tex_2])).
% 0.21/0.47  thf('0', plain, ((~ (v1_tdlat_3 @ sk_A) | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, (~ ((v1_tdlat_3 @ sk_A)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain, (((v1_tdlat_3 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(t2_tsep_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: ((m1_pre_topc @ X0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.47  thf('5', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t26_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.47          | ((X3) != (u1_struct_0 @ X1))
% 0.21/0.47          | ~ (v2_tex_2 @ X3 @ X2)
% 0.21/0.47          | (v1_tdlat_3 @ X1)
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.47          | ~ (l1_pre_topc @ X2)
% 0.21/0.47          | (v2_struct_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X2)
% 0.21/0.47          | ~ (l1_pre_topc @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.47          | (v1_tdlat_3 @ X1)
% 0.21/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ X1) @ X2)
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.47          | (v2_struct_0 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ sk_A)
% 0.21/0.47          | (v1_tdlat_3 @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.47  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ sk_A)
% 0.21/0.47          | (v1_tdlat_3 @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '15', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.21/0.47        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '18'])).
% 0.21/0.47  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ sk_A) | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, ((~ (v2_tex_2 @ sk_B @ sk_A) | (v1_tdlat_3 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, (((v1_tdlat_3 @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '23'])).
% 0.21/0.47  thf('25', plain, ((~ (v1_tdlat_3 @ sk_A)) <= (~ ((v1_tdlat_3 @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('26', plain, (((v1_tdlat_3 @ sk_A)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, (((v1_tdlat_3 @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('28', plain, (((v1_tdlat_3 @ sk_A)) <= (((v1_tdlat_3 @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i]: ((m1_pre_topc @ X0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.47  thf('30', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.47          | ((X3) != (u1_struct_0 @ X1))
% 0.21/0.47          | ~ (v1_tdlat_3 @ X1)
% 0.21/0.47          | (v2_tex_2 @ X3 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.47          | ~ (l1_pre_topc @ X2)
% 0.21/0.47          | (v2_struct_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X2)
% 0.21/0.47          | ~ (l1_pre_topc @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.47          | (v2_tex_2 @ (u1_struct_0 @ X1) @ X2)
% 0.21/0.47          | ~ (v1_tdlat_3 @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.47          | (v2_struct_0 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.47          | (v2_tex_2 @ (u1_struct_0 @ X0) @ sk_A)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.47  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.47          | (v2_tex_2 @ (u1_struct_0 @ X0) @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['30', '36'])).
% 0.21/0.47  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('39', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.21/0.47        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.47        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '41'])).
% 0.21/0.47  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.47  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('46', plain, ((~ (v1_tdlat_3 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.47  thf('47', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_tdlat_3 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '46'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      ((~ (v2_tex_2 @ sk_B @ sk_A)) <= (~ ((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('49', plain, (~ ((v1_tdlat_3 @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.47  thf('50', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '49'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
