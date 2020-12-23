%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IyFpQdOmyZ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 375 expanded)
%              Number of leaves         :   18 ( 117 expanded)
%              Depth                    :   12
%              Number of atoms          :  386 (2676 expanded)
%              Number of equality atoms :   25 ( 216 expanded)
%              Maximal formula depth    :   13 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t15_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ~ ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ A ) )
                & ( v1_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tex_2])).

thf('0',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('8',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('19',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('21',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('24',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('25',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ( v1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('43',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('46',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','44','45','46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['22','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IyFpQdOmyZ
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 55 iterations in 0.044s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(t15_tex_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( l1_pre_topc @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.20/0.52  thf('0', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_l1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('4', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf(fc12_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) =>
% 0.20/0.52       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X4 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ (k2_struct_0 @ X4) @ (u1_struct_0 @ X4))
% 0.20/0.52          | ~ (l1_struct_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.20/0.52        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('15', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('18', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((((k2_struct_0 @ sk_A) = (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('21', plain, (((k2_struct_0 @ sk_A) = (k2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '21'])).
% 0.20/0.52  thf('23', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf('24', plain, (((k2_struct_0 @ sk_A) = (k2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('25', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf('28', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (((k2_struct_0 @ sk_A) = (k2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('30', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf(t13_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.52                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.20/0.52                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X7 @ X8)
% 0.20/0.52          | ((X9) != (u1_struct_0 @ X7))
% 0.20/0.52          | ~ (v1_tex_2 @ X7 @ X8)
% 0.20/0.52          | (v1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.52          | ~ (l1_pre_topc @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X8)
% 0.20/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.52          | (v1_subset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X8))
% 0.20/0.52          | ~ (v1_tex_2 @ X7 @ X8)
% 0.20/0.52          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.20/0.52          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.52  thf('34', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.20/0.52          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.20/0.52        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.20/0.52        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '36'])).
% 0.20/0.52  thf('38', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t1_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X5) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.52          | ~ (l1_pre_topc @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('43', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.20/0.52  thf('45', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('46', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '44', '45', '46', '47'])).
% 0.20/0.52  thf('49', plain, ($false), inference('demod', [status(thm)], ['22', '48'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
