%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7KUQSen8fk

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 (  99 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  505 (1472 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

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
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
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
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t23_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_tdlat_3 @ X10 )
      | ~ ( v3_pre_topc @ X11 @ X10 )
      | ( v4_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_tdlat_3 @ X8 )
      | ( v3_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_tdlat_3 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_tdlat_3 @ X8 )
      | ( v3_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( sk_B_2 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ( v3_pre_topc @ ( sk_B_2 @ X0 ) @ X0 )
      | ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B_2 @ X12 ) @ X12 )
      | ( v3_tdlat_3 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( v3_tdlat_3 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','27'])).

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

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ ( sk_D @ X5 @ X4 @ X6 ) ) @ X6 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_3 )
    | ~ ( l1_pre_topc @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_3 ),
    inference(demod,[status(thm)],['30','31','32','33','34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7KUQSen8fk
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:18:33 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 37 iterations in 0.022s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.19/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.47  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.19/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.19/0.47  thf(t68_tex_2, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.47                 ( m1_subset_1 @
% 0.19/0.47                   C @ 
% 0.19/0.47                   ( k1_zfmisc_1 @
% 0.19/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.47               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.47                    ( v1_funct_2 @
% 0.19/0.47                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.47                    ( m1_subset_1 @
% 0.19/0.47                      C @ 
% 0.19/0.47                      ( k1_zfmisc_1 @
% 0.19/0.47                        ( k2_zfmisc_1 @
% 0.19/0.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.47                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 0.19/0.47  thf('0', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_3)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(dt_k8_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.19/0.47          | (m1_subset_1 @ (k8_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.19/0.47             (k1_zfmisc_1 @ X1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (m1_subset_1 @ 
% 0.19/0.47          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47           sk_C @ X0) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf(t23_tdlat_3, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ( v3_tdlat_3 @ A ) <=>
% 0.19/0.47         ( ![B:$i]:
% 0.19/0.47           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i]:
% 0.19/0.47         (~ (v3_tdlat_3 @ X10)
% 0.19/0.47          | ~ (v3_pre_topc @ X11 @ X10)
% 0.19/0.47          | (v4_pre_topc @ X11 @ X10)
% 0.19/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.19/0.47          | ~ (l1_pre_topc @ X10)
% 0.19/0.47          | ~ (v2_pre_topc @ X10))),
% 0.19/0.47      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v2_pre_topc @ sk_A)
% 0.19/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.47          | (v4_pre_topc @ 
% 0.19/0.47             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47              sk_C @ X0) @ 
% 0.19/0.47             sk_A)
% 0.19/0.47          | ~ (v3_pre_topc @ 
% 0.19/0.47               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47                sk_C @ X0) @ 
% 0.19/0.47               sk_A)
% 0.19/0.47          | ~ (v3_tdlat_3 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (m1_subset_1 @ 
% 0.19/0.47          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47           sk_C @ X0) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf(t17_tdlat_3, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ( v1_tdlat_3 @ A ) <=>
% 0.19/0.47         ( ![B:$i]:
% 0.19/0.47           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (v1_tdlat_3 @ X8)
% 0.19/0.47          | (v3_pre_topc @ X9 @ X8)
% 0.19/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.47          | ~ (l1_pre_topc @ X8)
% 0.19/0.47          | ~ (v2_pre_topc @ X8))),
% 0.19/0.47      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v2_pre_topc @ sk_A)
% 0.19/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.47          | (v3_pre_topc @ 
% 0.19/0.47             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47              sk_C @ X0) @ 
% 0.19/0.47             sk_A)
% 0.19/0.47          | ~ (v1_tdlat_3 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('13', plain, ((v1_tdlat_3 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (v3_pre_topc @ 
% 0.19/0.47          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47           sk_C @ X0) @ 
% 0.19/0.47          sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v4_pre_topc @ 
% 0.19/0.47           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47            sk_C @ X0) @ 
% 0.19/0.47           sk_A)
% 0.19/0.47          | ~ (v3_tdlat_3 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '6', '7', '14'])).
% 0.19/0.47  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t24_tdlat_3, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ( v3_tdlat_3 @ A ) <=>
% 0.19/0.47         ( ![B:$i]:
% 0.19/0.47           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X12 : $i]:
% 0.19/0.47         ((m1_subset_1 @ (sk_B_2 @ X12) @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.47          | (v3_tdlat_3 @ X12)
% 0.19/0.47          | ~ (l1_pre_topc @ X12)
% 0.19/0.47          | ~ (v2_pre_topc @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (v1_tdlat_3 @ X8)
% 0.19/0.47          | (v3_pre_topc @ X9 @ X8)
% 0.19/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.47          | ~ (l1_pre_topc @ X8)
% 0.19/0.47          | ~ (v2_pre_topc @ X8))),
% 0.19/0.47      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v2_pre_topc @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | (v3_tdlat_3 @ X0)
% 0.19/0.47          | ~ (v2_pre_topc @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | (v3_pre_topc @ (sk_B_2 @ X0) @ X0)
% 0.19/0.47          | ~ (v1_tdlat_3 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_tdlat_3 @ X0)
% 0.19/0.47          | (v3_pre_topc @ (sk_B_2 @ X0) @ X0)
% 0.19/0.47          | (v3_tdlat_3 @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | ~ (v2_pre_topc @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X12 : $i]:
% 0.19/0.47         (~ (v3_pre_topc @ (sk_B_2 @ X12) @ X12)
% 0.19/0.47          | (v3_tdlat_3 @ X12)
% 0.19/0.47          | ~ (l1_pre_topc @ X12)
% 0.19/0.47          | ~ (v2_pre_topc @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v2_pre_topc @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | (v3_tdlat_3 @ X0)
% 0.19/0.47          | ~ (v1_tdlat_3 @ X0)
% 0.19/0.47          | ~ (v2_pre_topc @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | (v3_tdlat_3 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_tdlat_3 @ X0)
% 0.19/0.47          | (v3_tdlat_3 @ X0)
% 0.19/0.47          | ~ (l1_pre_topc @ X0)
% 0.19/0.47          | ~ (v2_pre_topc @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      ((~ (v2_pre_topc @ sk_A) | (v3_tdlat_3 @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['16', '23'])).
% 0.19/0.47  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('26', plain, ((v1_tdlat_3 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('27', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (v4_pre_topc @ 
% 0.19/0.47          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3) @ 
% 0.19/0.47           sk_C @ X0) @ 
% 0.19/0.47          sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['15', '27'])).
% 0.19/0.47  thf(d12_pre_topc, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( l1_pre_topc @ B ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.47                 ( m1_subset_1 @
% 0.19/0.47                   C @ 
% 0.19/0.47                   ( k1_zfmisc_1 @
% 0.19/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.47               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.19/0.47                 ( ![D:$i]:
% 0.19/0.47                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.47                     ( ( v4_pre_topc @ D @ B ) =>
% 0.19/0.47                       ( v4_pre_topc @
% 0.19/0.47                         ( k8_relset_1 @
% 0.19/0.47                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.19/0.47                         A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X4)
% 0.19/0.47          | ~ (v4_pre_topc @ 
% 0.19/0.47               (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ 
% 0.19/0.47                (sk_D @ X5 @ X4 @ X6)) @ 
% 0.19/0.47               X6)
% 0.19/0.47          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ 
% 0.19/0.47               (k1_zfmisc_1 @ 
% 0.19/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.19/0.47          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.19/0.47          | ~ (v1_funct_1 @ X5)
% 0.19/0.47          | ~ (l1_pre_topc @ X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))
% 0.19/0.47        | ~ (m1_subset_1 @ sk_C @ 
% 0.19/0.47             (k1_zfmisc_1 @ 
% 0.19/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))
% 0.19/0.47        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_3)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_B_3))),
% 0.19/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.47  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_3))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('35', plain, ((l1_pre_topc @ sk_B_3)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('36', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B_3)),
% 0.19/0.47      inference('demod', [status(thm)], ['30', '31', '32', '33', '34', '35'])).
% 0.19/0.47  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
