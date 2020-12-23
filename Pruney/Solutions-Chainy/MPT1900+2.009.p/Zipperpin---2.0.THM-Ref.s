%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TtMDcil324

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  85 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  445 (1083 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X4 @ X5 @ X6 @ X7 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X4 @ X5 @ X6 @ X7 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_tdlat_3 @ X13 )
      | ( v4_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_tdlat_3 @ X13 )
      | ( v4_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k9_setfam_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

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

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X9 @ ( sk_D @ X9 @ X8 @ X10 ) ) @ X10 )
      | ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X9 @ ( sk_D @ X9 @ X8 @ X10 ) ) @ X10 )
      | ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('30',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TtMDcil324
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 33 iterations in 0.021s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.45  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.45  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.45  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.45  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.45  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(t68_tex_2, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.45           ( ![C:$i]:
% 0.21/0.45             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.45                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.45                 ( m1_subset_1 @
% 0.21/0.45                   C @ 
% 0.21/0.45                   ( k1_zfmisc_1 @
% 0.21/0.45                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.45               ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( ( ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45          ( ![B:$i]:
% 0.21/0.45            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.45              ( ![C:$i]:
% 0.21/0.45                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.45                    ( v1_funct_2 @
% 0.21/0.45                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.45                    ( m1_subset_1 @
% 0.21/0.45                      C @ 
% 0.21/0.45                      ( k1_zfmisc_1 @
% 0.21/0.45                        ( k2_zfmisc_1 @
% 0.21/0.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.45                  ( v5_pre_topc @ C @ A @ B ) ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t68_tex_2])).
% 0.21/0.45  thf('0', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_C @ 
% 0.21/0.45        (k1_zfmisc_1 @ 
% 0.21/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.45    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.45  thf('2', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_C @ 
% 0.21/0.45        (k9_setfam_1 @ 
% 0.21/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.45      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf(t47_funct_2, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.45       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.45         ((r1_tarski @ (k8_relset_1 @ X4 @ X5 @ X6 @ X7) @ X4)
% 0.21/0.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.45          | ~ (v1_funct_1 @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.21/0.45  thf('5', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.45         ((r1_tarski @ (k8_relset_1 @ X4 @ X5 @ X6 @ X7) @ X4)
% 0.21/0.45          | ~ (m1_subset_1 @ X6 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.45          | ~ (v1_funct_1 @ X6))),
% 0.21/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v1_funct_1 @ sk_C)
% 0.21/0.45          | (r1_tarski @ 
% 0.21/0.45             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.45              sk_C @ X0) @ 
% 0.21/0.45             (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.45  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (r1_tarski @ 
% 0.21/0.45          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.45           sk_C @ X0) @ 
% 0.21/0.45          (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('11', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         ((m1_subset_1 @ X0 @ (k9_setfam_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (m1_subset_1 @ 
% 0.21/0.45          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.45           sk_C @ X0) @ 
% 0.21/0.45          (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.45  thf(t18_tdlat_3, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ( v1_tdlat_3 @ A ) <=>
% 0.21/0.45         ( ![B:$i]:
% 0.21/0.45           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X13 : $i, X14 : $i]:
% 0.21/0.45         (~ (v1_tdlat_3 @ X13)
% 0.21/0.45          | (v4_pre_topc @ X14 @ X13)
% 0.21/0.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.45          | ~ (l1_pre_topc @ X13)
% 0.21/0.45          | ~ (v2_pre_topc @ X13))),
% 0.21/0.45      inference('cnf', [status(esa)], [t18_tdlat_3])).
% 0.21/0.45  thf('15', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      (![X13 : $i, X14 : $i]:
% 0.21/0.45         (~ (v1_tdlat_3 @ X13)
% 0.21/0.45          | (v4_pre_topc @ X14 @ X13)
% 0.21/0.45          | ~ (m1_subset_1 @ X14 @ (k9_setfam_1 @ (u1_struct_0 @ X13)))
% 0.21/0.45          | ~ (l1_pre_topc @ X13)
% 0.21/0.45          | ~ (v2_pre_topc @ X13))),
% 0.21/0.45      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v2_pre_topc @ sk_A)
% 0.21/0.45          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45          | (v4_pre_topc @ 
% 0.21/0.45             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.45              sk_C @ X0) @ 
% 0.21/0.45             sk_A)
% 0.21/0.45          | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.45  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('20', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (v4_pre_topc @ 
% 0.21/0.45          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.45           sk_C @ X0) @ 
% 0.21/0.45          sk_A)),
% 0.21/0.45      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.21/0.45  thf(d12_pre_topc, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( l1_pre_topc @ A ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( l1_pre_topc @ B ) =>
% 0.21/0.45           ( ![C:$i]:
% 0.21/0.45             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.45                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.45                 ( m1_subset_1 @
% 0.21/0.45                   C @ 
% 0.21/0.45                   ( k1_zfmisc_1 @
% 0.21/0.45                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.45               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.45                 ( ![D:$i]:
% 0.21/0.45                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.45                     ( ( v4_pre_topc @ D @ B ) =>
% 0.21/0.45                       ( v4_pre_topc @
% 0.21/0.45                         ( k8_relset_1 @
% 0.21/0.45                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.21/0.45                         A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.45  thf('22', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.45         (~ (l1_pre_topc @ X8)
% 0.21/0.45          | ~ (v4_pre_topc @ 
% 0.21/0.45               (k8_relset_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ X9 @ 
% 0.21/0.45                (sk_D @ X9 @ X8 @ X10)) @ 
% 0.21/0.45               X10)
% 0.21/0.45          | (v5_pre_topc @ X9 @ X10 @ X8)
% 0.21/0.45          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.45               (k1_zfmisc_1 @ 
% 0.21/0.45                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.21/0.45          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.21/0.45          | ~ (v1_funct_1 @ X9)
% 0.21/0.45          | ~ (l1_pre_topc @ X10))),
% 0.21/0.45      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.45  thf('23', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.45  thf('24', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.45         (~ (l1_pre_topc @ X8)
% 0.21/0.45          | ~ (v4_pre_topc @ 
% 0.21/0.45               (k8_relset_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ X9 @ 
% 0.21/0.45                (sk_D @ X9 @ X8 @ X10)) @ 
% 0.21/0.45               X10)
% 0.21/0.45          | (v5_pre_topc @ X9 @ X10 @ X8)
% 0.21/0.45          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.45               (k9_setfam_1 @ 
% 0.21/0.45                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.21/0.45          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.21/0.45          | ~ (v1_funct_1 @ X9)
% 0.21/0.45          | ~ (l1_pre_topc @ X10))),
% 0.21/0.45      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.45  thf('25', plain,
% 0.21/0.45      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.21/0.45        | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.45             (k9_setfam_1 @ 
% 0.21/0.45              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.45        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.45  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('28', plain,
% 0.21/0.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('29', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_C @ 
% 0.21/0.45        (k9_setfam_1 @ 
% 0.21/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.45      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('30', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('31', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.45      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.21/0.45  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
