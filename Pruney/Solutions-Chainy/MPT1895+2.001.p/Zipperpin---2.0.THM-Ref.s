%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.llRJtQnth0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  73 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  290 ( 888 expanded)
%              Number of equality atoms :   14 (  40 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_0_tex_2_type,type,(
    a_2_0_tex_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t63_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
           => ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
             => ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) )
                = ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_tops_1 @ X0 @ X1 )
      | ( ( k2_pre_topc @ X1 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_tops_1 @ X4 @ X5 )
      | ~ ( v3_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tdlat_3 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t62_tex_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','14'])).

thf('16',plain,(
    ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = ( k3_tarski @ ( a_2_0_tex_2 @ X3 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v3_tdlat_3 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t54_tex_2])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k3_tarski @ ( a_2_0_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_pre_topc @ sk_A @ sk_B )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.llRJtQnth0
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:37:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 15 iterations in 0.012s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.43  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.19/0.43  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.19/0.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.43  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.19/0.43  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.43  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.43  thf(a_2_0_tex_2_type, type, a_2_0_tex_2: $i > $i > $i).
% 0.19/0.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.43  thf(t63_tex_2, conjecture,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.43         ( l1_pre_topc @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.43           ( ( v3_tex_2 @ B @ A ) =>
% 0.19/0.43             ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ![A:$i]:
% 0.19/0.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.43            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.43          ( ![B:$i]:
% 0.19/0.43            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.43              ( ( v3_tex_2 @ B @ A ) =>
% 0.19/0.43                ( ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) = ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t63_tex_2])).
% 0.19/0.43  thf('0', plain,
% 0.19/0.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(d2_tops_3, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( l1_pre_topc @ A ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.43           ( ( v1_tops_1 @ B @ A ) <=>
% 0.19/0.43             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]:
% 0.19/0.43         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.43          | ~ (v1_tops_1 @ X0 @ X1)
% 0.19/0.43          | ((k2_pre_topc @ X1 @ X0) = (u1_struct_0 @ X1))
% 0.19/0.43          | ~ (l1_pre_topc @ X1))),
% 0.19/0.43      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.43        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.19/0.43        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.19/0.43      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.43  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('4', plain,
% 0.19/0.43      ((((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.19/0.43        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.19/0.43      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.43  thf('5', plain,
% 0.19/0.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(t62_tex_2, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.43         ( l1_pre_topc @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.43           ( ( v3_tex_2 @ B @ A ) => ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (![X4 : $i, X5 : $i]:
% 0.19/0.43         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.43          | (v1_tops_1 @ X4 @ X5)
% 0.19/0.43          | ~ (v3_tex_2 @ X4 @ X5)
% 0.19/0.43          | ~ (l1_pre_topc @ X5)
% 0.19/0.43          | ~ (v3_tdlat_3 @ X5)
% 0.19/0.43          | ~ (v2_pre_topc @ X5)
% 0.19/0.43          | (v2_struct_0 @ X5))),
% 0.19/0.43      inference('cnf', [status(esa)], [t62_tex_2])).
% 0.19/0.43  thf('7', plain,
% 0.19/0.43      (((v2_struct_0 @ sk_A)
% 0.19/0.43        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.43        | ~ (v3_tdlat_3 @ sk_A)
% 0.19/0.43        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.43        | ~ (v3_tex_2 @ sk_B @ sk_A)
% 0.19/0.43        | (v1_tops_1 @ sk_B @ sk_A))),
% 0.19/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.43  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('9', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('11', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('12', plain, (((v2_struct_0 @ sk_A) | (v1_tops_1 @ sk_B @ sk_A))),
% 0.19/0.43      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.19/0.43  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.19/0.43      inference('clc', [status(thm)], ['12', '13'])).
% 0.19/0.43  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.19/0.43      inference('demod', [status(thm)], ['4', '14'])).
% 0.19/0.43  thf('16', plain,
% 0.19/0.43      (((k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('17', plain,
% 0.19/0.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(t54_tex_2, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.43         ( l1_pre_topc @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.43           ( ( k2_pre_topc @ A @ B ) = ( k3_tarski @ ( a_2_0_tex_2 @ A @ B ) ) ) ) ) ))).
% 0.19/0.43  thf('18', plain,
% 0.19/0.43      (![X2 : $i, X3 : $i]:
% 0.19/0.43         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.19/0.43          | ((k2_pre_topc @ X3 @ X2) = (k3_tarski @ (a_2_0_tex_2 @ X3 @ X2)))
% 0.19/0.43          | ~ (l1_pre_topc @ X3)
% 0.19/0.43          | ~ (v3_tdlat_3 @ X3)
% 0.19/0.43          | ~ (v2_pre_topc @ X3)
% 0.19/0.43          | (v2_struct_0 @ X3))),
% 0.19/0.43      inference('cnf', [status(esa)], [t54_tex_2])).
% 0.19/0.43  thf('19', plain,
% 0.19/0.43      (((v2_struct_0 @ sk_A)
% 0.19/0.43        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.43        | ~ (v3_tdlat_3 @ sk_A)
% 0.19/0.43        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.43        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.19/0.43            = (k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B))))),
% 0.19/0.43      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.43  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('21', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('23', plain,
% 0.19/0.43      (((v2_struct_0 @ sk_A)
% 0.19/0.43        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.19/0.43            = (k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B))))),
% 0.19/0.43      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.19/0.43  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('25', plain,
% 0.19/0.43      (((k2_pre_topc @ sk_A @ sk_B) = (k3_tarski @ (a_2_0_tex_2 @ sk_A @ sk_B)))),
% 0.19/0.43      inference('clc', [status(thm)], ['23', '24'])).
% 0.19/0.43  thf('26', plain, (((k2_pre_topc @ sk_A @ sk_B) != (u1_struct_0 @ sk_A))),
% 0.19/0.43      inference('demod', [status(thm)], ['16', '25'])).
% 0.19/0.43  thf('27', plain, ($false),
% 0.19/0.43      inference('simplify_reflect-', [status(thm)], ['15', '26'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
