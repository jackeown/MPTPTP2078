%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xfk56ODMC3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 131 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   21
%              Number of atoms          :  511 (2027 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k8_filter_1_type,type,(
    k8_filter_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r1_filter_1_type,type,(
    r1_filter_1: $i > $i > $o )).

thf(t34_filter_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v10_lattices @ C )
                & ( l3_lattices @ C ) )
             => ( ( ( r1_filter_1 @ A @ B )
                  & ( r1_filter_1 @ B @ C ) )
               => ( r1_filter_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( l3_lattices @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v10_lattices @ C )
                  & ( l3_lattices @ C ) )
               => ( ( ( r1_filter_1 @ A @ B )
                    & ( r1_filter_1 @ B @ C ) )
                 => ( r1_filter_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_filter_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( v1_relat_1 @ ( k8_filter_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k8_filter_1 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_filter_1])).

thf('2',plain,(
    r1_filter_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( r1_filter_1 @ A @ B )
          <=> ( r4_wellord1 @ ( k8_filter_1 @ A ) @ ( k8_filter_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( r1_filter_1 @ X4 @ X3 )
      | ( r4_wellord1 @ ( k8_filter_1 @ X4 ) @ ( k8_filter_1 @ X3 ) )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_filter_1])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ ( k8_filter_1 @ sk_C ) )
    | ~ ( l3_lattices @ sk_C )
    | ~ ( v10_lattices @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l3_lattices @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v10_lattices @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ ( k8_filter_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ ( k8_filter_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ ( k8_filter_1 @ sk_C ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k8_filter_1 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_filter_1])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k8_filter_1 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_filter_1])).

thf('16',plain,(
    r1_filter_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( r1_filter_1 @ X4 @ X3 )
      | ( r4_wellord1 @ ( k8_filter_1 @ X4 ) @ ( k8_filter_1 @ X3 ) )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_filter_1])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_B ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ~ ( r4_wellord1 @ X0 @ X2 )
      | ( r4_wellord1 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k8_filter_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_filter_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v1_relat_1 @ ( k8_filter_1 @ sk_B ) )
      | ~ ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ X0 )
      | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_relat_1 @ ( k8_filter_1 @ sk_B ) )
      | ~ ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ X0 )
      | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k8_filter_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k8_filter_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( v10_lattices @ sk_C )
    | ~ ( l3_lattices @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','38'])).

thf('40',plain,(
    v10_lattices @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l3_lattices @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r4_wellord1 @ ( k8_filter_1 @ sk_A ) @ ( k8_filter_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( r4_wellord1 @ ( k8_filter_1 @ X4 ) @ ( k8_filter_1 @ X3 ) )
      | ( r1_filter_1 @ X4 @ X3 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_filter_1])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_filter_1 @ sk_A @ sk_C )
    | ~ ( l3_lattices @ sk_C )
    | ~ ( v10_lattices @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l3_lattices @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v10_lattices @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_filter_1 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ( r1_filter_1 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( r1_filter_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xfk56ODMC3
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 24 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.46  thf(k8_filter_1_type, type, k8_filter_1: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.46  thf(r1_filter_1_type, type, r1_filter_1: $i > $i > $o).
% 0.20/0.46  thf(t34_filter_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.20/0.46             ( l3_lattices @ B ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( ( ~( v2_struct_0 @ C ) ) & ( v10_lattices @ C ) & 
% 0.20/0.46                 ( l3_lattices @ C ) ) =>
% 0.20/0.46               ( ( ( r1_filter_1 @ A @ B ) & ( r1_filter_1 @ B @ C ) ) =>
% 0.20/0.46                 ( r1_filter_1 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.46            ( l3_lattices @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.20/0.46                ( l3_lattices @ B ) ) =>
% 0.20/0.46              ( ![C:$i]:
% 0.20/0.46                ( ( ( ~( v2_struct_0 @ C ) ) & ( v10_lattices @ C ) & 
% 0.20/0.46                    ( l3_lattices @ C ) ) =>
% 0.20/0.46                  ( ( ( r1_filter_1 @ A @ B ) & ( r1_filter_1 @ B @ C ) ) =>
% 0.20/0.46                    ( r1_filter_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t34_filter_1])).
% 0.20/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_k8_filter_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.46       ( v1_relat_1 @ ( k8_filter_1 @ A ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X5 : $i]:
% 0.20/0.46         ((v1_relat_1 @ (k8_filter_1 @ X5))
% 0.20/0.46          | ~ (l3_lattices @ X5)
% 0.20/0.46          | ~ (v10_lattices @ X5)
% 0.20/0.46          | (v2_struct_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k8_filter_1])).
% 0.20/0.46  thf('2', plain, ((r1_filter_1 @ sk_B @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d9_filter_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.20/0.46             ( l3_lattices @ B ) ) =>
% 0.20/0.46           ( ( r1_filter_1 @ A @ B ) <=>
% 0.20/0.46             ( r4_wellord1 @ ( k8_filter_1 @ A ) @ ( k8_filter_1 @ B ) ) ) ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X3)
% 0.20/0.46          | ~ (v10_lattices @ X3)
% 0.20/0.46          | ~ (l3_lattices @ X3)
% 0.20/0.46          | ~ (r1_filter_1 @ X4 @ X3)
% 0.20/0.46          | (r4_wellord1 @ (k8_filter_1 @ X4) @ (k8_filter_1 @ X3))
% 0.20/0.46          | ~ (l3_lattices @ X4)
% 0.20/0.46          | ~ (v10_lattices @ X4)
% 0.20/0.46          | (v2_struct_0 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d9_filter_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_B)
% 0.20/0.46        | ~ (v10_lattices @ sk_B)
% 0.20/0.46        | ~ (l3_lattices @ sk_B)
% 0.20/0.46        | (r4_wellord1 @ (k8_filter_1 @ sk_B) @ (k8_filter_1 @ sk_C))
% 0.20/0.46        | ~ (l3_lattices @ sk_C)
% 0.20/0.46        | ~ (v10_lattices @ sk_C)
% 0.20/0.46        | (v2_struct_0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain, ((v10_lattices @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain, ((l3_lattices @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain, ((l3_lattices @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain, ((v10_lattices @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_B)
% 0.20/0.46        | (r4_wellord1 @ (k8_filter_1 @ sk_B) @ (k8_filter_1 @ sk_C))
% 0.20/0.46        | (v2_struct_0 @ sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.46  thf('10', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_C)
% 0.20/0.46        | (r4_wellord1 @ (k8_filter_1 @ sk_B) @ (k8_filter_1 @ sk_C)))),
% 0.20/0.46      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((r4_wellord1 @ (k8_filter_1 @ sk_B) @ (k8_filter_1 @ sk_C))),
% 0.20/0.46      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X5 : $i]:
% 0.20/0.46         ((v1_relat_1 @ (k8_filter_1 @ X5))
% 0.20/0.46          | ~ (l3_lattices @ X5)
% 0.20/0.46          | ~ (v10_lattices @ X5)
% 0.20/0.46          | (v2_struct_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k8_filter_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X5 : $i]:
% 0.20/0.46         ((v1_relat_1 @ (k8_filter_1 @ X5))
% 0.20/0.46          | ~ (l3_lattices @ X5)
% 0.20/0.46          | ~ (v10_lattices @ X5)
% 0.20/0.46          | (v2_struct_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k8_filter_1])).
% 0.20/0.46  thf('16', plain, ((r1_filter_1 @ sk_A @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((v2_struct_0 @ X3)
% 0.20/0.46          | ~ (v10_lattices @ X3)
% 0.20/0.46          | ~ (l3_lattices @ X3)
% 0.20/0.46          | ~ (r1_filter_1 @ X4 @ X3)
% 0.20/0.46          | (r4_wellord1 @ (k8_filter_1 @ X4) @ (k8_filter_1 @ X3))
% 0.20/0.46          | ~ (l3_lattices @ X4)
% 0.20/0.46          | ~ (v10_lattices @ X4)
% 0.20/0.46          | (v2_struct_0 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d9_filter_1])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | ~ (v10_lattices @ sk_A)
% 0.20/0.46        | ~ (l3_lattices @ sk_A)
% 0.20/0.46        | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_B))
% 0.20/0.46        | ~ (l3_lattices @ sk_B)
% 0.20/0.46        | ~ (v10_lattices @ sk_B)
% 0.20/0.46        | (v2_struct_0 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain, ((v10_lattices @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('21', plain, ((l3_lattices @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('22', plain, ((v10_lattices @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_A)
% 0.20/0.46        | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_B))
% 0.20/0.46        | (v2_struct_0 @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.20/0.46  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (((v2_struct_0 @ sk_B)
% 0.20/0.46        | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_B)))),
% 0.20/0.46      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.46  thf('26', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      ((r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_B))),
% 0.20/0.46      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.46  thf(t52_wellord1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( v1_relat_1 @ B ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( v1_relat_1 @ C ) =>
% 0.20/0.46               ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.20/0.46                 ( r4_wellord1 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (r4_wellord1 @ X1 @ X0)
% 0.20/0.46          | ~ (r4_wellord1 @ X0 @ X2)
% 0.20/0.46          | (r4_wellord1 @ X1 @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ X2)
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ (k8_filter_1 @ sk_A))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ X0)
% 0.20/0.46          | ~ (r4_wellord1 @ (k8_filter_1 @ sk_B) @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ (k8_filter_1 @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_A)
% 0.20/0.46          | ~ (v10_lattices @ sk_A)
% 0.20/0.46          | ~ (l3_lattices @ sk_A)
% 0.20/0.46          | ~ (v1_relat_1 @ (k8_filter_1 @ sk_B))
% 0.20/0.46          | ~ (r4_wellord1 @ (k8_filter_1 @ sk_B) @ X0)
% 0.20/0.46          | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['15', '29'])).
% 0.20/0.46  thf('31', plain, ((v10_lattices @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('32', plain, ((l3_lattices @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_A)
% 0.20/0.46          | ~ (v1_relat_1 @ (k8_filter_1 @ sk_B))
% 0.20/0.46          | ~ (r4_wellord1 @ (k8_filter_1 @ sk_B) @ X0)
% 0.20/0.46          | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_B)
% 0.20/0.46          | ~ (v10_lattices @ sk_B)
% 0.20/0.46          | ~ (l3_lattices @ sk_B)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ X0)
% 0.20/0.46          | ~ (r4_wellord1 @ (k8_filter_1 @ sk_B) @ X0)
% 0.20/0.46          | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '33'])).
% 0.20/0.46  thf('35', plain, ((v10_lattices @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain, ((l3_lattices @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ X0)
% 0.20/0.47          | ~ (r4_wellord1 @ (k8_filter_1 @ sk_B) @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_C))
% 0.20/0.47        | ~ (v1_relat_1 @ (k8_filter_1 @ sk_C))
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_C)
% 0.20/0.47        | ~ (v10_lattices @ sk_C)
% 0.20/0.47        | ~ (l3_lattices @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_C))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '38'])).
% 0.20/0.47  thf('40', plain, ((v10_lattices @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, ((l3_lattices @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (r4_wellord1 @ (k8_filter_1 @ sk_A) @ (k8_filter_1 @ sk_C))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X3)
% 0.20/0.47          | ~ (v10_lattices @ X3)
% 0.20/0.47          | ~ (l3_lattices @ X3)
% 0.20/0.47          | ~ (r4_wellord1 @ (k8_filter_1 @ X4) @ (k8_filter_1 @ X3))
% 0.20/0.47          | (r1_filter_1 @ X4 @ X3)
% 0.20/0.47          | ~ (l3_lattices @ X4)
% 0.20/0.47          | ~ (v10_lattices @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d9_filter_1])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v10_lattices @ sk_A)
% 0.20/0.47        | ~ (l3_lattices @ sk_A)
% 0.20/0.47        | (r1_filter_1 @ sk_A @ sk_C)
% 0.20/0.47        | ~ (l3_lattices @ sk_C)
% 0.20/0.47        | ~ (v10_lattices @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain, ((v10_lattices @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain, ((l3_lattices @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain, ((l3_lattices @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('48', plain, ((v10_lattices @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | (r1_filter_1 @ sk_A @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (((r1_filter_1 @ sk_A @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.47  thf('51', plain, (~ (r1_filter_1 @ sk_A @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.47  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('54', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.47  thf('55', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('56', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.47  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
