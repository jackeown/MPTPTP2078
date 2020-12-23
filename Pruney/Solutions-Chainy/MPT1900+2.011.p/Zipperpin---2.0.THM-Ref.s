%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LvSuzJxReD

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  295 ( 835 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t68_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( v5_pre_topc @ C @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( v5_pre_topc @ C @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_tex_2])).

thf('0',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_tdlat_3 @ X8 )
      | ( v4_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ ( sk_D @ X5 @ X4 @ X6 ) ) @ X6 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['11','12','13','14','15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LvSuzJxReD
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 16 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.46  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.46  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.46  thf(t68_tex_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.46                 ( m1_subset_1 @
% 0.21/0.46                   C @ 
% 0.21/0.46                   ( k1_zfmisc_1 @
% 0.21/0.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.46               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.46              ( ![C:$i]:
% 0.21/0.46                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.46                    ( v1_funct_2 @
% 0.21/0.46                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.46                    ( m1_subset_1 @
% 0.21/0.46                      C @ 
% 0.21/0.46                      ( k1_zfmisc_1 @
% 0.21/0.46                        ( k2_zfmisc_1 @
% 0.21/0.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.46                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 0.21/0.46  thf('0', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ 
% 0.21/0.46        (k1_zfmisc_1 @ 
% 0.21/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(dt_k8_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.46          | (m1_subset_1 @ (k8_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.21/0.46             (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (m1_subset_1 @ 
% 0.21/0.46          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.46           sk_C @ X0) @ 
% 0.21/0.46          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t18_tdlat_3, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.46       ( ( v1_tdlat_3 @ A ) <=>
% 0.21/0.46         ( ![B:$i]:
% 0.21/0.46           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i]:
% 0.21/0.46         (~ (v1_tdlat_3 @ X8)
% 0.21/0.46          | (v4_pre_topc @ X9 @ X8)
% 0.21/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.46          | ~ (l1_pre_topc @ X8)
% 0.21/0.46          | ~ (v2_pre_topc @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v2_pre_topc @ sk_A)
% 0.21/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.46          | (v4_pre_topc @ 
% 0.21/0.46             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.46              sk_C @ X0) @ 
% 0.21/0.46             sk_A)
% 0.21/0.46          | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (v4_pre_topc @ 
% 0.21/0.46          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.46           sk_C @ X0) @ 
% 0.21/0.46          sk_A)),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.46  thf(d12_pre_topc, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( l1_pre_topc @ B ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.46                 ( m1_subset_1 @
% 0.21/0.46                   C @ 
% 0.21/0.46                   ( k1_zfmisc_1 @
% 0.21/0.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.46               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.46                 ( ![D:$i]:
% 0.21/0.46                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.46                     ( ( v4_pre_topc @ D @ B ) =>
% 0.21/0.46                       ( v4_pre_topc @
% 0.21/0.46                         ( k8_relset_1 @
% 0.21/0.46                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.21/0.46                         A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         (~ (l1_pre_topc @ X4)
% 0.21/0.46          | ~ (v4_pre_topc @ 
% 0.21/0.46               (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ 
% 0.21/0.46                (sk_D @ X5 @ X4 @ X6)) @ 
% 0.21/0.46               X6)
% 0.21/0.46          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.21/0.46          | ~ (m1_subset_1 @ X5 @ 
% 0.21/0.46               (k1_zfmisc_1 @ 
% 0.21/0.46                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.21/0.46          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.21/0.46          | ~ (v1_funct_1 @ X5)
% 0.21/0.46          | ~ (l1_pre_topc @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.21/0.46        | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.46             (k1_zfmisc_1 @ 
% 0.21/0.46              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.46        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.21/0.46        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ 
% 0.21/0.46        (k1_zfmisc_1 @ 
% 0.21/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('16', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '16'])).
% 0.21/0.46  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
