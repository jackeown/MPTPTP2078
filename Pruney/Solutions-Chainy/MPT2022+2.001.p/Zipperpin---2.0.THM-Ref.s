%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IONI6AkeAO

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:25 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 158 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  475 (2109 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t21_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
               => ( m1_connsp_2 @ C @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ? [D: $i] :
                  ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ B @ D )
                  & ( D = C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ ( k9_yellow_6 @ X4 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( ( sk_D @ X5 @ X3 @ X4 )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ ( k9_yellow_6 @ X4 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D @ sk_C @ sk_B @ sk_A )
      = sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( m1_connsp_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( v3_pre_topc @ ( sk_D @ X5 @ X3 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ ( k9_yellow_6 @ X4 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['13','14'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r2_hidden @ X3 @ ( sk_D @ X5 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ ( k9_yellow_6 @ X4 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['13','14'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IONI6AkeAO
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:40:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 17 iterations in 0.019s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.18/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.46  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 0.18/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.46  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(t21_waybel_9, conjecture,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.46           ( ![C:$i]:
% 0.18/0.46             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 0.18/0.46               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i]:
% 0.18/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.46            ( l1_pre_topc @ A ) ) =>
% 0.18/0.46          ( ![B:$i]:
% 0.18/0.46            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.46              ( ![C:$i]:
% 0.18/0.46                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 0.18/0.46                  ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t21_waybel_9])).
% 0.18/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t38_yellow_6, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.46           ( ![C:$i]:
% 0.18/0.46             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 0.18/0.46               ( ?[D:$i]:
% 0.18/0.46                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 0.18/0.46                   ( ( D ) = ( C ) ) & 
% 0.18/0.46                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.18/0.46          | (m1_subset_1 @ (sk_D @ X5 @ X3 @ X4) @ 
% 0.18/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.18/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ (k9_yellow_6 @ X4 @ X3)))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t38_yellow_6])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.18/0.46           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.46        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.46  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.18/0.46          | ((sk_D @ X5 @ X3 @ X4) = (X5))
% 0.18/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ (k9_yellow_6 @ X4 @ X3)))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t38_yellow_6])).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | ((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))
% 0.18/0.46        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.46  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('13', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 0.18/0.46      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.18/0.46  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('15', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 0.18/0.46      inference('clc', [status(thm)], ['13', '14'])).
% 0.18/0.46  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('17', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.18/0.46      inference('demod', [status(thm)], ['4', '5', '6', '15', '16'])).
% 0.18/0.46  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('19', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.46      inference('clc', [status(thm)], ['17', '18'])).
% 0.18/0.46  thf(t5_connsp_2, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.46           ( ![C:$i]:
% 0.18/0.46             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.46               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.18/0.46                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.18/0.46          | ~ (v3_pre_topc @ X0 @ X1)
% 0.18/0.46          | ~ (r2_hidden @ X2 @ X0)
% 0.18/0.46          | (m1_connsp_2 @ X0 @ X1 @ X2)
% 0.18/0.46          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.18/0.46          | ~ (l1_pre_topc @ X1)
% 0.18/0.46          | ~ (v2_pre_topc @ X1)
% 0.18/0.46          | (v2_struct_0 @ X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((v2_struct_0 @ sk_A)
% 0.18/0.46          | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.18/0.46          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.18/0.46          | ~ (r2_hidden @ X0 @ sk_C)
% 0.18/0.46          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.18/0.46  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('24', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((v2_struct_0 @ sk_A)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.18/0.46          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.18/0.46          | ~ (r2_hidden @ X0 @ sk_C)
% 0.18/0.46          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.18/0.46  thf('25', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.18/0.46          | (v3_pre_topc @ (sk_D @ X5 @ X3 @ X4) @ X4)
% 0.18/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ (k9_yellow_6 @ X4 @ X3)))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t38_yellow_6])).
% 0.18/0.46  thf('27', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.18/0.46        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.18/0.46  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('30', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 0.18/0.46      inference('clc', [status(thm)], ['13', '14'])).
% 0.18/0.46  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('32', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.18/0.46  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('34', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.18/0.46      inference('clc', [status(thm)], ['32', '33'])).
% 0.18/0.46  thf('35', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((v2_struct_0 @ sk_A)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.18/0.46          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.18/0.46          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.18/0.46      inference('demod', [status(thm)], ['24', '34'])).
% 0.18/0.46  thf('36', plain,
% 0.18/0.46      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.18/0.46        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '35'])).
% 0.18/0.46  thf('37', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('38', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.18/0.46          | (r2_hidden @ X3 @ (sk_D @ X5 @ X3 @ X4))
% 0.18/0.46          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ (k9_yellow_6 @ X4 @ X3)))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t38_yellow_6])).
% 0.18/0.46  thf('39', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (r2_hidden @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.18/0.46        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.18/0.46  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('42', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 0.18/0.46      inference('clc', [status(thm)], ['13', '14'])).
% 0.18/0.46  thf('43', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('44', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 0.18/0.46      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.18/0.46  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('46', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.18/0.46      inference('clc', [status(thm)], ['44', '45'])).
% 0.18/0.46  thf('47', plain,
% 0.18/0.46      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['36', '46'])).
% 0.18/0.46  thf('48', plain, (~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('clc', [status(thm)], ['47', '48'])).
% 0.18/0.46  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
