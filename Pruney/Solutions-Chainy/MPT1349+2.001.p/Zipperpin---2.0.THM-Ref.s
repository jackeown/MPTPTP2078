%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rPOs90jJX9

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:30 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  278 (3775 expanded)
%              Number of leaves         :   41 (1093 expanded)
%              Depth                    :   29
%              Number of atoms          : 5007 (162849 expanded)
%              Number of equality atoms :  157 (5934 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t74_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ A @ D ) )
                        = ( k2_pre_topc @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_tops_2 @ C @ A @ B )
                <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ A ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ A @ D ) )
                          = ( k2_pre_topc @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_tops_2])).

thf('0',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('3',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tops_2 @ X17 @ X18 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X29 @ X27 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X29 ) @ X27 ) )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X29 )
       != ( k2_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t67_tops_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','22','23','24','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tops_2 @ X17 @ X18 @ X16 )
      | ( v2_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','41'])).

thf('43',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('44',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X19 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

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

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v5_pre_topc @ X8 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X19 @ X20 @ X21 ) @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','65','71','72'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('75',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v4_pre_topc @ ( sk_D @ X8 @ X7 @ X9 ) @ X7 )
      | ( v5_pre_topc @ X8 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('83',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['77','85'])).

thf('87',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','65','71','72'])).

thf('88',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('89',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('93',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X4 @ X5 @ X3 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_pre_topc @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
       != X14 )
      | ( v4_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) )
       != ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) )
      | ~ ( v2_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) )
       != ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
       != ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ( ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','65','71','72'])).

thf('103',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('104',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','22','23','24','27'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ sk_C )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['103','107'])).

thf('109',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X8 @ ( sk_D @ X8 @ X7 @ X9 ) ) @ X9 )
      | ( v5_pre_topc @ X8 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('111',plain,
    ( ( ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('114',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116'])).

thf('118',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['101','118'])).

thf('120',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 )
       != ( k2_struct_0 @ X18 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v5_pre_topc @ X17 @ X18 @ X16 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 ) @ X16 @ X18 )
      | ( v3_tops_2 @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('131',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tops_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ A @ D ) ) @ ( k2_pre_topc @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) )).

thf('133',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( m1_subset_1 @ ( sk_D_1 @ X23 @ X22 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v5_pre_topc @ X23 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('134',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('145',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X23 @ ( k2_pre_topc @ X24 @ ( sk_D_1 @ X23 @ X22 @ X24 ) ) ) @ ( k2_pre_topc @ X22 @ ( k7_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X23 @ ( sk_D_1 @ X23 @ X22 @ X24 ) ) ) )
      | ( v5_pre_topc @ X23 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('147',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['147','149','150','151','152','153','154','155','156'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','160'])).

thf('162',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','162'])).

thf('164',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['165'])).

thf('167',plain,
    ( ~ ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X37 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X37 ) ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['164','166'])).

thf('168',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','167'])).

thf('169',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tops_2 @ X17 @ X18 @ X16 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('172',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['169','177'])).

thf('179',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['165'])).

thf('180',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('183',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['165'])).

thf('184',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('186',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['165'])).

thf('187',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('190',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['181','184','188','43','45','47','49','167','189'])).

thf('191',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) ) ),
    inference(simpl_trail,[status(thm)],['42','168','190'])).

thf('192',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('193',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['181','184','188','43','45','47','49','167','189'])).

thf('194',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['192','193'])).

thf('195',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf(t73_tops_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ B @ D ) )
                        = ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) )).

thf('196',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v3_tops_2 @ X35 @ X34 @ X33 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 @ ( k2_pre_topc @ X33 @ X36 ) )
        = ( k2_pre_topc @ X34 @ ( k8_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('201',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202','203'])).

thf('205',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('206',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
               => ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) )).

thf('207',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v3_tops_2 @ X31 @ X32 @ X30 )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ X31 ) @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_tops_2])).

thf('208',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['208','209','210','211','212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['205','215'])).

thf('217',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','167'])).

thf('218',plain,(
    v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['204','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['194','221'])).

thf('223',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('224',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf('225',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_3 ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','167'])).

thf('227',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['181','184','188','43','45','47','49','167','189'])).

thf('228',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_3 ) ),
    inference(simpl_trail,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['222','228'])).

thf('230',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['191','229'])).

thf('231',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
   <= ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ) ),
    inference(split,[status(esa)],['165'])).

thf('232',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['165'])).

thf('233',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
 != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','167','188','184','181','232'])).

thf('234',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
 != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ),
    inference(simpl_trail,[status(thm)],['231','233'])).

thf('235',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['230','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rPOs90jJX9
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.13  % Solved by: fo/fo7.sh
% 0.91/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.13  % done 989 iterations in 0.678s
% 0.91/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.13  % SZS output start Refutation
% 0.91/1.13  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.91/1.13  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.91/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.13  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.91/1.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.91/1.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.13  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.13  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.91/1.13  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.91/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.13  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.91/1.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.13  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.91/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.13  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.91/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.13  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.13  thf(t74_tops_2, conjecture,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.91/1.13             ( l1_pre_topc @ B ) ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                 ( m1_subset_1 @
% 0.91/1.13                   C @ 
% 0.91/1.13                   ( k1_zfmisc_1 @
% 0.91/1.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.91/1.13                 ( ( ( k1_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                     ( k2_struct_0 @ A ) ) & 
% 0.91/1.13                   ( ( k2_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                   ( v2_funct_1 @ C ) & 
% 0.91/1.13                   ( ![D:$i]:
% 0.91/1.13                     ( ( m1_subset_1 @
% 0.91/1.13                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13                       ( ( k7_relset_1 @
% 0.91/1.13                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.91/1.13                           ( k2_pre_topc @ A @ D ) ) =
% 0.91/1.13                         ( k2_pre_topc @
% 0.91/1.13                           B @ 
% 0.91/1.13                           ( k7_relset_1 @
% 0.91/1.13                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.13    (~( ![A:$i]:
% 0.91/1.13        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.13          ( ![B:$i]:
% 0.91/1.13            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.91/1.13                ( l1_pre_topc @ B ) ) =>
% 0.91/1.13              ( ![C:$i]:
% 0.91/1.13                ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                    ( v1_funct_2 @
% 0.91/1.13                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                    ( m1_subset_1 @
% 0.91/1.13                      C @ 
% 0.91/1.13                      ( k1_zfmisc_1 @
% 0.91/1.13                        ( k2_zfmisc_1 @
% 0.91/1.13                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13                  ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.91/1.13                    ( ( ( k1_relset_1 @
% 0.91/1.13                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                        ( k2_struct_0 @ A ) ) & 
% 0.91/1.13                      ( ( k2_relset_1 @
% 0.91/1.13                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                        ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                      ( v2_funct_1 @ C ) & 
% 0.91/1.13                      ( ![D:$i]:
% 0.91/1.13                        ( ( m1_subset_1 @
% 0.91/1.13                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13                          ( ( k7_relset_1 @
% 0.91/1.13                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.91/1.13                              ( k2_pre_topc @ A @ D ) ) =
% 0.91/1.13                            ( k2_pre_topc @
% 0.91/1.13                              B @ 
% 0.91/1.13                              ( k7_relset_1 @
% 0.91/1.13                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.91/1.13                                C @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.91/1.13    inference('cnf.neg', [status(esa)], [t74_tops_2])).
% 0.91/1.13  thf('0', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_B))
% 0.91/1.13        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_A))
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('1', plain,
% 0.91/1.13      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('split', [status(esa)], ['0'])).
% 0.91/1.13  thf(dt_k2_pre_topc, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.13       ( m1_subset_1 @
% 0.91/1.13         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.13  thf('2', plain,
% 0.91/1.13      (![X11 : $i, X12 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X11)
% 0.91/1.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.13          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 0.91/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.13  thf('3', plain,
% 0.91/1.13      ((((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_3) @ 
% 0.91/1.13          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13         | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.13         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.13  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('5', plain,
% 0.91/1.13      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_3) @ 
% 0.91/1.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('demod', [status(thm)], ['3', '4'])).
% 0.91/1.13  thf('6', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A))
% 0.91/1.13        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('7', plain,
% 0.91/1.13      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('split', [status(esa)], ['6'])).
% 0.91/1.13  thf('8', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(d5_tops_2, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( l1_pre_topc @ B ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                 ( m1_subset_1 @
% 0.91/1.13                   C @ 
% 0.91/1.13                   ( k1_zfmisc_1 @
% 0.91/1.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.91/1.13                 ( ( ( k1_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                     ( k2_struct_0 @ A ) ) & 
% 0.91/1.13                   ( ( k2_relset_1 @
% 0.91/1.13                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.91/1.13                   ( v5_pre_topc @
% 0.91/1.13                     ( k2_tops_2 @
% 0.91/1.13                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.91/1.13                     B @ A ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('9', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X16)
% 0.91/1.13          | ~ (v3_tops_2 @ X17 @ X18 @ X16)
% 0.91/1.13          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17)
% 0.91/1.13              = (k2_struct_0 @ X16))
% 0.91/1.13          | ~ (m1_subset_1 @ X17 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.91/1.13          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.91/1.13          | ~ (v1_funct_1 @ X17)
% 0.91/1.13          | ~ (l1_pre_topc @ X18))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.91/1.13  thf('10', plain,
% 0.91/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            = (k2_struct_0 @ sk_B))
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (l1_pre_topc @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.13  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('13', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('15', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B))
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.91/1.13  thf('16', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B)))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['7', '15'])).
% 0.91/1.13  thf('17', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(t67_tops_2, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_struct_0 @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( l1_struct_0 @ B ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                 ( m1_subset_1 @
% 0.91/1.13                   C @ 
% 0.91/1.13                   ( k1_zfmisc_1 @
% 0.91/1.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13               ( ![D:$i]:
% 0.91/1.13                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13                   ( ( ( ( k2_relset_1 @
% 0.91/1.13                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.13                         ( k2_struct_0 @ B ) ) & 
% 0.91/1.13                       ( v2_funct_1 @ C ) ) =>
% 0.91/1.13                     ( ( k7_relset_1 @
% 0.91/1.13                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.91/1.13                       ( k8_relset_1 @
% 0.91/1.13                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.13                         ( k2_tops_2 @
% 0.91/1.13                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.91/1.13                         D ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('18', plain,
% 0.91/1.13      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.13         (~ (l1_struct_0 @ X26)
% 0.91/1.13          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.91/1.13          | ((k7_relset_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ X29 @ 
% 0.91/1.13              X27)
% 0.91/1.13              = (k8_relset_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28) @ 
% 0.91/1.13                 (k2_tops_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ X29) @ 
% 0.91/1.13                 X27))
% 0.91/1.13          | ~ (v2_funct_1 @ X29)
% 0.91/1.13          | ((k2_relset_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ X29)
% 0.91/1.13              != (k2_struct_0 @ X26))
% 0.91/1.13          | ~ (m1_subset_1 @ X29 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 0.91/1.13          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 0.91/1.13          | ~ (v1_funct_1 @ X29)
% 0.91/1.13          | ~ (l1_struct_0 @ X28))),
% 0.91/1.13      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.91/1.13  thf('19', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_struct_0 @ sk_A)
% 0.91/1.13          | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13              != (k2_struct_0 @ sk_B))
% 0.91/1.13          | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ X0)
% 0.91/1.13              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C) @ 
% 0.91/1.13                 X0))
% 0.91/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13          | ~ (l1_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.13  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(dt_l1_pre_topc, axiom,
% 0.91/1.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.91/1.13  thf('21', plain,
% 0.91/1.13      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.91/1.13  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.13      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.13  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('24', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('26', plain,
% 0.91/1.13      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.91/1.13  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('28', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_B))
% 0.91/1.13          | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ X0)
% 0.91/1.13              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C) @ 
% 0.91/1.13                 X0))
% 0.91/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['19', '22', '23', '24', '27'])).
% 0.91/1.13  thf('29', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.91/1.13           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0)
% 0.91/1.13               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  X0))
% 0.91/1.13           | ~ (v2_funct_1 @ sk_C)))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['16', '28'])).
% 0.91/1.13  thf('30', plain,
% 0.91/1.13      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('split', [status(esa)], ['6'])).
% 0.91/1.13  thf('31', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('32', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X16)
% 0.91/1.13          | ~ (v3_tops_2 @ X17 @ X18 @ X16)
% 0.91/1.13          | (v2_funct_1 @ X17)
% 0.91/1.13          | ~ (m1_subset_1 @ X17 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.91/1.13          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.91/1.13          | ~ (v1_funct_1 @ X17)
% 0.91/1.13          | ~ (l1_pre_topc @ X18))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.91/1.13  thf('33', plain,
% 0.91/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | (v2_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (l1_pre_topc @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.13  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('36', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('38', plain,
% 0.91/1.13      (((v2_funct_1 @ sk_C) | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.91/1.13  thf('39', plain,
% 0.91/1.13      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['30', '38'])).
% 0.91/1.13  thf('40', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.91/1.13           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0)
% 0.91/1.13               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  X0))))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('demod', [status(thm)], ['29', '39'])).
% 0.91/1.13  thf('41', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ X0)
% 0.91/1.13             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13                X0))
% 0.91/1.13           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['40'])).
% 0.91/1.13  thf('42', plain,
% 0.91/1.13      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.13          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             (k2_pre_topc @ sk_A @ sk_D_3))))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.91/1.13             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['5', '41'])).
% 0.91/1.13  thf('43', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A))) | 
% 0.91/1.13       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('split', [status(esa)], ['6'])).
% 0.91/1.13  thf('44', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B))
% 0.91/1.13        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('45', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B))) | 
% 0.91/1.13       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('split', [status(esa)], ['44'])).
% 0.91/1.13  thf('46', plain, (((v2_funct_1 @ sk_C) | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('47', plain,
% 0.91/1.13      (((v2_funct_1 @ sk_C)) | ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('split', [status(esa)], ['46'])).
% 0.91/1.13  thf('48', plain,
% 0.91/1.13      (![X37 : $i]:
% 0.91/1.13         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13              = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                 (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C @ X37)))
% 0.91/1.13          | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('49', plain,
% 0.91/1.13      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.91/1.13       (![X37 : $i]:
% 0.91/1.13          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13               = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C @ X37)))))),
% 0.91/1.13      inference('split', [status(esa)], ['48'])).
% 0.91/1.13  thf('50', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('split', [status(esa)], ['6'])).
% 0.91/1.13  thf('51', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(dt_k2_tops_2, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.13       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.91/1.13         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.91/1.13         ( m1_subset_1 @
% 0.91/1.13           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.91/1.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.91/1.13  thf('52', plain,
% 0.91/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.13         ((m1_subset_1 @ (k2_tops_2 @ X19 @ X20 @ X21) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.91/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.91/1.13          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.91/1.13          | ~ (v1_funct_1 @ X21))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.91/1.13  thf('53', plain,
% 0.91/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | (m1_subset_1 @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13           (k1_zfmisc_1 @ 
% 0.91/1.13            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['51', '52'])).
% 0.91/1.13  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('55', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('56', plain,
% 0.91/1.13      ((m1_subset_1 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.91/1.13  thf(d12_pre_topc, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( l1_pre_topc @ B ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                 ( m1_subset_1 @
% 0.91/1.13                   C @ 
% 0.91/1.13                   ( k1_zfmisc_1 @
% 0.91/1.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.91/1.13                 ( ![D:$i]:
% 0.91/1.13                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.91/1.13                     ( ( v4_pre_topc @ D @ B ) =>
% 0.91/1.13                       ( v4_pre_topc @
% 0.91/1.13                         ( k8_relset_1 @
% 0.91/1.13                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.91/1.13                         A ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('57', plain,
% 0.91/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X7)
% 0.91/1.13          | (m1_subset_1 @ (sk_D @ X8 @ X7 @ X9) @ 
% 0.91/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.91/1.13          | (v5_pre_topc @ X8 @ X9 @ X7)
% 0.91/1.13          | ~ (m1_subset_1 @ X8 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.91/1.13          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.91/1.13          | ~ (v1_funct_1 @ X8)
% 0.91/1.13          | ~ (l1_pre_topc @ X9))),
% 0.91/1.13      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.91/1.13  thf('58', plain,
% 0.91/1.13      ((~ (l1_pre_topc @ sk_B)
% 0.91/1.13        | ~ (v1_funct_1 @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13        | ~ (v1_funct_2 @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.13        | (v5_pre_topc @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13           sk_B @ sk_A)
% 0.91/1.13        | (m1_subset_1 @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.13      inference('sup-', [status(thm)], ['56', '57'])).
% 0.91/1.13  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('60', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('61', plain,
% 0.91/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.13         ((v1_funct_1 @ (k2_tops_2 @ X19 @ X20 @ X21))
% 0.91/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.91/1.13          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.91/1.13          | ~ (v1_funct_1 @ X21))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.91/1.13  thf('62', plain,
% 0.91/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | (v1_funct_1 @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.13  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('64', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('65', plain,
% 0.91/1.13      ((v1_funct_1 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.91/1.13  thf('66', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('67', plain,
% 0.91/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.13         ((v1_funct_2 @ (k2_tops_2 @ X19 @ X20 @ X21) @ X20 @ X19)
% 0.91/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.91/1.13          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.91/1.13          | ~ (v1_funct_1 @ X21))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.91/1.13  thf('68', plain,
% 0.91/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | (v1_funct_2 @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.13  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('70', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('71', plain,
% 0.91/1.13      ((v1_funct_2 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.91/1.13  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('73', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A)
% 0.91/1.13        | (m1_subset_1 @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['58', '59', '65', '71', '72'])).
% 0.91/1.13  thf(t52_pre_topc, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_pre_topc @ A ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.91/1.13             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.91/1.13               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.91/1.13  thf('74', plain,
% 0.91/1.13      (![X14 : $i, X15 : $i]:
% 0.91/1.13         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.91/1.13          | ~ (v4_pre_topc @ X14 @ X15)
% 0.91/1.13          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.91/1.13          | ~ (l1_pre_topc @ X15))),
% 0.91/1.13      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.91/1.13  thf('75', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A)
% 0.91/1.13        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.13        | ((k2_pre_topc @ sk_A @ 
% 0.91/1.13            (sk_D @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             sk_A @ sk_B))
% 0.91/1.13            = (sk_D @ 
% 0.91/1.13               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13               sk_A @ sk_B))
% 0.91/1.13        | ~ (v4_pre_topc @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B) @ 
% 0.91/1.13             sk_A))),
% 0.91/1.13      inference('sup-', [status(thm)], ['73', '74'])).
% 0.91/1.13  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('77', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A)
% 0.91/1.13        | ((k2_pre_topc @ sk_A @ 
% 0.91/1.13            (sk_D @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             sk_A @ sk_B))
% 0.91/1.13            = (sk_D @ 
% 0.91/1.13               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13               sk_A @ sk_B))
% 0.91/1.13        | ~ (v4_pre_topc @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B) @ 
% 0.91/1.13             sk_A))),
% 0.91/1.13      inference('demod', [status(thm)], ['75', '76'])).
% 0.91/1.13  thf('78', plain,
% 0.91/1.13      ((m1_subset_1 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.91/1.13  thf('79', plain,
% 0.91/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X7)
% 0.91/1.13          | (v4_pre_topc @ (sk_D @ X8 @ X7 @ X9) @ X7)
% 0.91/1.13          | (v5_pre_topc @ X8 @ X9 @ X7)
% 0.91/1.13          | ~ (m1_subset_1 @ X8 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.91/1.13          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.91/1.13          | ~ (v1_funct_1 @ X8)
% 0.91/1.13          | ~ (l1_pre_topc @ X9))),
% 0.91/1.13      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.91/1.13  thf('80', plain,
% 0.91/1.13      ((~ (l1_pre_topc @ sk_B)
% 0.91/1.13        | ~ (v1_funct_1 @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13        | ~ (v1_funct_2 @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.13        | (v5_pre_topc @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13           sk_B @ sk_A)
% 0.91/1.13        | (v4_pre_topc @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B) @ 
% 0.91/1.13           sk_A)
% 0.91/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.13      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.13  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('82', plain,
% 0.91/1.13      ((v1_funct_1 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.91/1.13  thf('83', plain,
% 0.91/1.13      ((v1_funct_2 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.91/1.13  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('85', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A)
% 0.91/1.13        | (v4_pre_topc @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B) @ 
% 0.91/1.13           sk_A))),
% 0.91/1.13      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.91/1.13  thf('86', plain,
% 0.91/1.13      ((((k2_pre_topc @ sk_A @ 
% 0.91/1.13          (sk_D @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13           sk_A @ sk_B))
% 0.91/1.13          = (sk_D @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             sk_A @ sk_B))
% 0.91/1.13        | (v5_pre_topc @ 
% 0.91/1.13           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13           sk_B @ sk_A))),
% 0.91/1.13      inference('clc', [status(thm)], ['77', '85'])).
% 0.91/1.13  thf('87', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A)
% 0.91/1.13        | (m1_subset_1 @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['58', '59', '65', '71', '72'])).
% 0.91/1.13  thf('88', plain,
% 0.91/1.13      ((![X37 : $i]:
% 0.91/1.13          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13               = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C @ X37)))))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('split', [status(esa)], ['48'])).
% 0.91/1.13  thf('89', plain,
% 0.91/1.13      ((((v5_pre_topc @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13          sk_B @ sk_A)
% 0.91/1.13         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ 
% 0.91/1.13             (k2_pre_topc @ sk_A @ 
% 0.91/1.13              (sk_D @ 
% 0.91/1.13               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13               sk_A @ sk_B)))
% 0.91/1.13             = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                 sk_C @ 
% 0.91/1.13                 (sk_D @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  sk_A @ sk_B))))))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['87', '88'])).
% 0.91/1.13  thf('90', plain,
% 0.91/1.13      (((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B))
% 0.91/1.13           = (k2_pre_topc @ sk_B @ 
% 0.91/1.13              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ 
% 0.91/1.13               (sk_D @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13                sk_A @ sk_B))))
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup+', [status(thm)], ['86', '89'])).
% 0.91/1.13  thf('91', plain,
% 0.91/1.13      ((((v5_pre_topc @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13          sk_B @ sk_A)
% 0.91/1.13         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B))
% 0.91/1.13             = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                 sk_C @ 
% 0.91/1.13                 (sk_D @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  sk_A @ sk_B))))))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['90'])).
% 0.91/1.13  thf('92', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(dt_k7_relset_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.13       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.91/1.13  thf('93', plain,
% 0.91/1.13      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.13         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.91/1.13          | (m1_subset_1 @ (k7_relset_1 @ X4 @ X5 @ X3 @ X6) @ 
% 0.91/1.13             (k1_zfmisc_1 @ X5)))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.91/1.13  thf('94', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (m1_subset_1 @ 
% 0.91/1.13          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13           X0) @ 
% 0.91/1.13          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['92', '93'])).
% 0.91/1.13  thf('95', plain,
% 0.91/1.13      (![X14 : $i, X15 : $i]:
% 0.91/1.13         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.91/1.13          | ~ (v2_pre_topc @ X15)
% 0.91/1.13          | ((k2_pre_topc @ X15 @ X14) != (X14))
% 0.91/1.13          | (v4_pre_topc @ X14 @ X15)
% 0.91/1.13          | ~ (l1_pre_topc @ X15))),
% 0.91/1.13      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.91/1.13  thf('96', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ sk_B)
% 0.91/1.13          | (v4_pre_topc @ 
% 0.91/1.13             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ X0) @ 
% 0.91/1.13             sk_B)
% 0.91/1.13          | ((k2_pre_topc @ sk_B @ 
% 0.91/1.13              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0))
% 0.91/1.13              != (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C @ X0))
% 0.91/1.13          | ~ (v2_pre_topc @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['94', '95'])).
% 0.91/1.13  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('99', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((v4_pre_topc @ 
% 0.91/1.13           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13            X0) @ 
% 0.91/1.13           sk_B)
% 0.91/1.13          | ((k2_pre_topc @ sk_B @ 
% 0.91/1.13              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0))
% 0.91/1.13              != (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C @ X0)))),
% 0.91/1.13      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.91/1.13  thf('100', plain,
% 0.91/1.13      (((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B))
% 0.91/1.13           != (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ 
% 0.91/1.13               (sk_D @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13                sk_A @ sk_B)))
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)
% 0.91/1.13         | (v4_pre_topc @ 
% 0.91/1.13            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B)) @ 
% 0.91/1.13            sk_B)))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['91', '99'])).
% 0.91/1.13  thf('101', plain,
% 0.91/1.13      ((((v4_pre_topc @ 
% 0.91/1.13          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B)) @ 
% 0.91/1.13          sk_B)
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['100'])).
% 0.91/1.13  thf('102', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A)
% 0.91/1.13        | (m1_subset_1 @ 
% 0.91/1.13           (sk_D @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_A @ sk_B) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['58', '59', '65', '71', '72'])).
% 0.91/1.13  thf('103', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('split', [status(esa)], ['46'])).
% 0.91/1.13  thf('104', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('split', [status(esa)], ['44'])).
% 0.91/1.13  thf('105', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_B))
% 0.91/1.13          | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ X0)
% 0.91/1.13              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C) @ 
% 0.91/1.13                 X0))
% 0.91/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['19', '22', '23', '24', '27'])).
% 0.91/1.13  thf('106', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.91/1.13           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0)
% 0.91/1.13               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  X0))
% 0.91/1.13           | ~ (v2_funct_1 @ sk_C)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['104', '105'])).
% 0.91/1.13  thf('107', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (v2_funct_1 @ sk_C)
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0)
% 0.91/1.13               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  X0))
% 0.91/1.13           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['106'])).
% 0.91/1.13  thf('108', plain,
% 0.91/1.13      ((![X0 : $i]:
% 0.91/1.13          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ X0)
% 0.91/1.13               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C) @ 
% 0.91/1.13                  X0))))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['103', '107'])).
% 0.91/1.13  thf('109', plain,
% 0.91/1.13      ((((v5_pre_topc @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13          sk_B @ sk_A)
% 0.91/1.13         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B))
% 0.91/1.13             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13                (sk_D @ 
% 0.91/1.13                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                  sk_C) @ 
% 0.91/1.13                 sk_A @ sk_B)))))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['102', '108'])).
% 0.91/1.13  thf('110', plain,
% 0.91/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X7)
% 0.91/1.13          | ~ (v4_pre_topc @ 
% 0.91/1.13               (k8_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X8 @ 
% 0.91/1.13                (sk_D @ X8 @ X7 @ X9)) @ 
% 0.91/1.13               X9)
% 0.91/1.13          | (v5_pre_topc @ X8 @ X9 @ X7)
% 0.91/1.13          | ~ (m1_subset_1 @ X8 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.91/1.13          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.91/1.13          | ~ (v1_funct_1 @ X8)
% 0.91/1.13          | ~ (l1_pre_topc @ X9))),
% 0.91/1.13      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.91/1.13  thf('111', plain,
% 0.91/1.13      (((~ (v4_pre_topc @ 
% 0.91/1.13            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B)) @ 
% 0.91/1.13            sk_B)
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)
% 0.91/1.13         | ~ (l1_pre_topc @ sk_B)
% 0.91/1.13         | ~ (v1_funct_1 @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.13         | ~ (v1_funct_2 @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.13         | ~ (m1_subset_1 @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              (k1_zfmisc_1 @ 
% 0.91/1.13               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)
% 0.91/1.13         | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['109', '110'])).
% 0.91/1.13  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('113', plain,
% 0.91/1.13      ((v1_funct_1 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.91/1.13  thf('114', plain,
% 0.91/1.13      ((v1_funct_2 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.91/1.13  thf('115', plain,
% 0.91/1.13      ((m1_subset_1 @ 
% 0.91/1.13        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.91/1.13      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.91/1.13  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('117', plain,
% 0.91/1.13      (((~ (v4_pre_topc @ 
% 0.91/1.13            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ 
% 0.91/1.13             (sk_D @ 
% 0.91/1.13              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13              sk_A @ sk_B)) @ 
% 0.91/1.13            sk_B)
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('demod', [status(thm)],
% 0.91/1.13                ['111', '112', '113', '114', '115', '116'])).
% 0.91/1.13  thf('118', plain,
% 0.91/1.13      ((((v5_pre_topc @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13          sk_B @ sk_A)
% 0.91/1.13         | ~ (v4_pre_topc @ 
% 0.91/1.13              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ 
% 0.91/1.13               (sk_D @ 
% 0.91/1.13                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13                sk_A @ sk_B)) @ 
% 0.91/1.13              sk_B)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['117'])).
% 0.91/1.13  thf('119', plain,
% 0.91/1.13      ((((v5_pre_topc @ 
% 0.91/1.13          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13          sk_B @ sk_A)
% 0.91/1.13         | (v5_pre_topc @ 
% 0.91/1.13            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13            sk_B @ sk_A)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['101', '118'])).
% 0.91/1.13  thf('120', plain,
% 0.91/1.13      (((v5_pre_topc @ 
% 0.91/1.13         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13         sk_B @ sk_A))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['119'])).
% 0.91/1.13  thf('121', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('122', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X16)
% 0.91/1.13          | ((k1_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17)
% 0.91/1.13              != (k2_struct_0 @ X18))
% 0.91/1.13          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17)
% 0.91/1.13              != (k2_struct_0 @ X16))
% 0.91/1.13          | ~ (v2_funct_1 @ X17)
% 0.91/1.13          | ~ (v5_pre_topc @ X17 @ X18 @ X16)
% 0.91/1.13          | ~ (v5_pre_topc @ 
% 0.91/1.13               (k2_tops_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17) @ 
% 0.91/1.13               X16 @ X18)
% 0.91/1.13          | (v3_tops_2 @ X17 @ X18 @ X16)
% 0.91/1.13          | ~ (m1_subset_1 @ X17 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.91/1.13          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.91/1.13          | ~ (v1_funct_1 @ X17)
% 0.91/1.13          | ~ (l1_pre_topc @ X18))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.91/1.13  thf('123', plain,
% 0.91/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (v5_pre_topc @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             sk_B @ sk_A)
% 0.91/1.13        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_B))
% 0.91/1.13        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_A))
% 0.91/1.13        | ~ (l1_pre_topc @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['121', '122'])).
% 0.91/1.13  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('126', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('127', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('128', plain,
% 0.91/1.13      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (v5_pre_topc @ 
% 0.91/1.13             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.13             sk_B @ sk_A)
% 0.91/1.13        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_B))
% 0.91/1.13        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_A)))),
% 0.91/1.13      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.91/1.13  thf('129', plain,
% 0.91/1.13      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13           != (k2_struct_0 @ sk_A))
% 0.91/1.13         | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13             != (k2_struct_0 @ sk_B))
% 0.91/1.13         | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['120', '128'])).
% 0.91/1.13  thf('130', plain,
% 0.91/1.13      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.91/1.13      inference('split', [status(esa)], ['44'])).
% 0.91/1.13  thf('131', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.91/1.13      inference('split', [status(esa)], ['46'])).
% 0.91/1.13  thf('132', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(t57_tops_2, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.91/1.13             ( l1_pre_topc @ B ) ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.13                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.13                 ( m1_subset_1 @
% 0.91/1.13                   C @ 
% 0.91/1.13                   ( k1_zfmisc_1 @
% 0.91/1.13                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.13               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.91/1.13                 ( ![D:$i]:
% 0.91/1.13                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.13                     ( r1_tarski @
% 0.91/1.13                       ( k7_relset_1 @
% 0.91/1.13                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.91/1.13                         ( k2_pre_topc @ A @ D ) ) @ 
% 0.91/1.13                       ( k2_pre_topc @
% 0.91/1.13                         B @ 
% 0.91/1.13                         ( k7_relset_1 @
% 0.91/1.13                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('133', plain,
% 0.91/1.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.13         ((v2_struct_0 @ X22)
% 0.91/1.13          | ~ (v2_pre_topc @ X22)
% 0.91/1.13          | ~ (l1_pre_topc @ X22)
% 0.91/1.13          | (m1_subset_1 @ (sk_D_1 @ X23 @ X22 @ X24) @ 
% 0.91/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.91/1.13          | (v5_pre_topc @ X23 @ X24 @ X22)
% 0.91/1.13          | ~ (m1_subset_1 @ X23 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 0.91/1.13          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 0.91/1.13          | ~ (v1_funct_1 @ X23)
% 0.91/1.13          | ~ (l1_pre_topc @ X24)
% 0.91/1.13          | ~ (v2_pre_topc @ X24))),
% 0.91/1.13      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.91/1.13  thf('134', plain,
% 0.91/1.13      ((~ (v2_pre_topc @ sk_A)
% 0.91/1.13        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13        | ~ (l1_pre_topc @ sk_B)
% 0.91/1.13        | ~ (v2_pre_topc @ sk_B)
% 0.91/1.13        | (v2_struct_0 @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['132', '133'])).
% 0.91/1.13  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('138', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('140', plain, ((v2_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('141', plain,
% 0.91/1.13      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.91/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13        | (v2_struct_0 @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)],
% 0.91/1.13                ['134', '135', '136', '137', '138', '139', '140'])).
% 0.91/1.13  thf('142', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('143', plain,
% 0.91/1.13      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.91/1.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('clc', [status(thm)], ['141', '142'])).
% 0.91/1.13  thf('144', plain,
% 0.91/1.13      ((![X37 : $i]:
% 0.91/1.13          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13               = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C @ X37)))))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('split', [status(esa)], ['48'])).
% 0.91/1.13  thf('145', plain,
% 0.91/1.13      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13             sk_C @ (k2_pre_topc @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.91/1.13             = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                 sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))))))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['143', '144'])).
% 0.91/1.13  thf('146', plain,
% 0.91/1.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.13         ((v2_struct_0 @ X22)
% 0.91/1.13          | ~ (v2_pre_topc @ X22)
% 0.91/1.13          | ~ (l1_pre_topc @ X22)
% 0.91/1.13          | ~ (r1_tarski @ 
% 0.91/1.13               (k7_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ 
% 0.91/1.13                X23 @ (k2_pre_topc @ X24 @ (sk_D_1 @ X23 @ X22 @ X24))) @ 
% 0.91/1.13               (k2_pre_topc @ X22 @ 
% 0.91/1.13                (k7_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ 
% 0.91/1.13                 X23 @ (sk_D_1 @ X23 @ X22 @ X24))))
% 0.91/1.13          | (v5_pre_topc @ X23 @ X24 @ X22)
% 0.91/1.13          | ~ (m1_subset_1 @ X23 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 0.91/1.13          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 0.91/1.13          | ~ (v1_funct_1 @ X23)
% 0.91/1.13          | ~ (l1_pre_topc @ X24)
% 0.91/1.13          | ~ (v2_pre_topc @ X24))),
% 0.91/1.13      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.91/1.13  thf('147', plain,
% 0.91/1.13      (((~ (r1_tarski @ 
% 0.91/1.13            (k2_pre_topc @ sk_B @ 
% 0.91/1.13             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))) @ 
% 0.91/1.13            (k2_pre_topc @ sk_B @ 
% 0.91/1.13             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13              sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))))
% 0.91/1.13         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | ~ (v2_pre_topc @ sk_A)
% 0.91/1.13         | ~ (l1_pre_topc @ sk_A)
% 0.91/1.13         | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13         | ~ (m1_subset_1 @ sk_C @ 
% 0.91/1.13              (k1_zfmisc_1 @ 
% 0.91/1.13               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.91/1.13         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | ~ (l1_pre_topc @ sk_B)
% 0.91/1.13         | ~ (v2_pre_topc @ sk_B)
% 0.91/1.13         | (v2_struct_0 @ sk_B)))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['145', '146'])).
% 0.91/1.13  thf(d10_xboole_0, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.13  thf('148', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.91/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.13  thf('149', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.13      inference('simplify', [status(thm)], ['148'])).
% 0.91/1.13  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('153', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('154', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('155', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('156', plain, ((v2_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('157', plain,
% 0.91/1.13      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | (v2_struct_0 @ sk_B)))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('demod', [status(thm)],
% 0.91/1.13                ['147', '149', '150', '151', '152', '153', '154', '155', '156'])).
% 0.91/1.13  thf('158', plain,
% 0.91/1.13      ((((v2_struct_0 @ sk_B) | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['157'])).
% 0.91/1.13  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('160', plain,
% 0.91/1.13      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.91/1.13         <= ((![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('clc', [status(thm)], ['158', '159'])).
% 0.91/1.13  thf('161', plain,
% 0.91/1.13      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13           != (k2_struct_0 @ sk_A))
% 0.91/1.13         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.91/1.13         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('demod', [status(thm)], ['129', '130', '131', '160'])).
% 0.91/1.13  thf('162', plain,
% 0.91/1.13      ((((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.13         | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13             != (k2_struct_0 @ sk_A))))
% 0.91/1.13         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['161'])).
% 0.91/1.13  thf('163', plain,
% 0.91/1.13      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.91/1.13         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.91/1.13         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['50', '162'])).
% 0.91/1.13  thf('164', plain,
% 0.91/1.13      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.91/1.13         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.91/1.13             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.13             ((v2_funct_1 @ sk_C)) & 
% 0.91/1.13             (![X37 : $i]:
% 0.91/1.13                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13                     = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.13                         (u1_struct_0 @ sk_B) @ sk_C @ X37))))))),
% 0.91/1.13      inference('simplify', [status(thm)], ['163'])).
% 0.91/1.13  thf('165', plain,
% 0.91/1.13      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.13          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.13          != (k2_pre_topc @ sk_B @ 
% 0.91/1.13              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ sk_D_3)))
% 0.91/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.13        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_B))
% 0.91/1.13        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            != (k2_struct_0 @ sk_A))
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('166', plain,
% 0.91/1.13      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.91/1.13         <= (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('split', [status(esa)], ['165'])).
% 0.91/1.13  thf('167', plain,
% 0.91/1.13      (~
% 0.91/1.13       (![X37 : $i]:
% 0.91/1.13          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.13           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13               sk_C @ (k2_pre_topc @ sk_A @ X37))
% 0.91/1.13               = (k2_pre_topc @ sk_B @ 
% 0.91/1.13                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                   sk_C @ X37))))) | 
% 0.91/1.13       ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.91/1.13       ~
% 0.91/1.13       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_B))) | 
% 0.91/1.13       ~
% 0.91/1.13       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A))) | 
% 0.91/1.13       ~ ((v2_funct_1 @ sk_C))),
% 0.91/1.13      inference('sup-', [status(thm)], ['164', '166'])).
% 0.91/1.13  thf('168', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('sat_resolution*', [status(thm)],
% 0.91/1.13                ['43', '45', '47', '49', '167'])).
% 0.91/1.13  thf('169', plain,
% 0.91/1.13      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('split', [status(esa)], ['6'])).
% 0.91/1.13  thf('170', plain,
% 0.91/1.13      ((m1_subset_1 @ sk_C @ 
% 0.91/1.13        (k1_zfmisc_1 @ 
% 0.91/1.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('171', plain,
% 0.91/1.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.13         (~ (l1_pre_topc @ X16)
% 0.91/1.13          | ~ (v3_tops_2 @ X17 @ X18 @ X16)
% 0.91/1.13          | ((k1_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17)
% 0.91/1.13              = (k2_struct_0 @ X18))
% 0.91/1.13          | ~ (m1_subset_1 @ X17 @ 
% 0.91/1.13               (k1_zfmisc_1 @ 
% 0.91/1.13                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.91/1.13          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.91/1.13          | ~ (v1_funct_1 @ X17)
% 0.91/1.13          | ~ (l1_pre_topc @ X18))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.91/1.13  thf('172', plain,
% 0.91/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.13        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.13        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13            = (k2_struct_0 @ sk_A))
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.13        | ~ (l1_pre_topc @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['170', '171'])).
% 0.91/1.13  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('175', plain,
% 0.91/1.13      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('176', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('177', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A))
% 0.91/1.13        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 0.91/1.13  thf('178', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['169', '177'])).
% 0.91/1.13  thf('179', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          != (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.91/1.13      inference('split', [status(esa)], ['165'])).
% 0.91/1.13  thf('180', plain,
% 0.91/1.13      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.91/1.13         <= (~
% 0.91/1.13             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.13                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.91/1.13             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['178', '179'])).
% 0.91/1.13  thf('181', plain,
% 0.91/1.13      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.13          = (k2_struct_0 @ sk_A))) | 
% 0.91/1.13       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.13      inference('simplify', [status(thm)], ['180'])).
% 0.91/1.13  thf('182', plain,
% 0.91/1.13      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['30', '38'])).
% 0.91/1.13  thf('183', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.91/1.14      inference('split', [status(esa)], ['165'])).
% 0.91/1.14  thf('184', plain,
% 0.91/1.14      (((v2_funct_1 @ sk_C)) | ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.14      inference('sup-', [status(thm)], ['182', '183'])).
% 0.91/1.14  thf('185', plain,
% 0.91/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B)))
% 0.91/1.14         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['7', '15'])).
% 0.91/1.14  thf('186', plain,
% 0.91/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          != (k2_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.91/1.14      inference('split', [status(esa)], ['165'])).
% 0.91/1.14  thf('187', plain,
% 0.91/1.14      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.91/1.14             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['185', '186'])).
% 0.91/1.14  thf('188', plain,
% 0.91/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B))) | 
% 0.91/1.14       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.14      inference('simplify', [status(thm)], ['187'])).
% 0.91/1.14  thf('189', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.91/1.14       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.91/1.14       ~
% 0.91/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B))) | 
% 0.91/1.14       ~ ((v2_funct_1 @ sk_C)) | 
% 0.91/1.14       ~
% 0.91/1.14       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_A)))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('190', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['181', '184', '188', '43', '45', '47', '49', '167', '189'])).
% 0.91/1.14  thf('191', plain,
% 0.91/1.14      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14         (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14         = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14            (k2_pre_topc @ sk_A @ sk_D_3)))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['42', '168', '190'])).
% 0.91/1.14  thf('192', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.14         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('193', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['181', '184', '188', '43', '45', '47', '49', '167', '189'])).
% 0.91/1.14  thf('194', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['192', '193'])).
% 0.91/1.14  thf('195', plain,
% 0.91/1.14      ((m1_subset_1 @ 
% 0.91/1.14        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.91/1.14  thf(t73_tops_2, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.91/1.14           ( ![C:$i]:
% 0.91/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.14                 ( m1_subset_1 @
% 0.91/1.14                   C @ 
% 0.91/1.14                   ( k1_zfmisc_1 @
% 0.91/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.14               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.91/1.14                 ( ( ( k1_relset_1 @
% 0.91/1.14                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.14                     ( k2_struct_0 @ A ) ) & 
% 0.91/1.14                   ( ( k2_relset_1 @
% 0.91/1.14                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.91/1.14                     ( k2_struct_0 @ B ) ) & 
% 0.91/1.14                   ( v2_funct_1 @ C ) & 
% 0.91/1.14                   ( ![D:$i]:
% 0.91/1.14                     ( ( m1_subset_1 @
% 0.91/1.14                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.91/1.14                       ( ( k8_relset_1 @
% 0.91/1.14                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.91/1.14                           ( k2_pre_topc @ B @ D ) ) =
% 0.91/1.14                         ( k2_pre_topc @
% 0.91/1.14                           A @ 
% 0.91/1.14                           ( k8_relset_1 @
% 0.91/1.14                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.14  thf('196', plain,
% 0.91/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.91/1.14         (~ (v2_pre_topc @ X33)
% 0.91/1.14          | ~ (l1_pre_topc @ X33)
% 0.91/1.14          | ~ (v3_tops_2 @ X35 @ X34 @ X33)
% 0.91/1.14          | ((k8_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35 @ 
% 0.91/1.14              (k2_pre_topc @ X33 @ X36))
% 0.91/1.14              = (k2_pre_topc @ X34 @ 
% 0.91/1.14                 (k8_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ 
% 0.91/1.14                  X35 @ X36)))
% 0.91/1.14          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.91/1.14          | ~ (m1_subset_1 @ X35 @ 
% 0.91/1.14               (k1_zfmisc_1 @ 
% 0.91/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.91/1.14          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.91/1.14          | ~ (v1_funct_1 @ X35)
% 0.91/1.14          | ~ (l1_pre_topc @ X34)
% 0.91/1.14          | ~ (v2_pre_topc @ X34)
% 0.91/1.14          | (v2_struct_0 @ X34))),
% 0.91/1.14      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.91/1.14  thf('197', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((v2_struct_0 @ sk_B)
% 0.91/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.91/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.91/1.14          | ~ (v1_funct_1 @ 
% 0.91/1.14               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.91/1.14          | ~ (v1_funct_2 @ 
% 0.91/1.14               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.14          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14              (k2_pre_topc @ sk_A @ X0))
% 0.91/1.14              = (k2_pre_topc @ sk_B @ 
% 0.91/1.14                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14                   sk_C) @ 
% 0.91/1.14                  X0)))
% 0.91/1.14          | ~ (v3_tops_2 @ 
% 0.91/1.14               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14               sk_B @ sk_A)
% 0.91/1.14          | ~ (l1_pre_topc @ sk_A)
% 0.91/1.14          | ~ (v2_pre_topc @ sk_A))),
% 0.91/1.14      inference('sup-', [status(thm)], ['195', '196'])).
% 0.91/1.14  thf('198', plain, ((v2_pre_topc @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('199', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('200', plain,
% 0.91/1.14      ((v1_funct_1 @ 
% 0.91/1.14        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.91/1.14  thf('201', plain,
% 0.91/1.14      ((v1_funct_2 @ 
% 0.91/1.14        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.91/1.14  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('204', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((v2_struct_0 @ sk_B)
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.14          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14              (k2_pre_topc @ sk_A @ X0))
% 0.91/1.14              = (k2_pre_topc @ sk_B @ 
% 0.91/1.14                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14                   sk_C) @ 
% 0.91/1.14                  X0)))
% 0.91/1.14          | ~ (v3_tops_2 @ 
% 0.91/1.14               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14               sk_B @ sk_A))),
% 0.91/1.14      inference('demod', [status(thm)],
% 0.91/1.14                ['197', '198', '199', '200', '201', '202', '203'])).
% 0.91/1.14  thf('205', plain,
% 0.91/1.14      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.91/1.14         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.14      inference('split', [status(esa)], ['6'])).
% 0.91/1.14  thf('206', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_C @ 
% 0.91/1.14        (k1_zfmisc_1 @ 
% 0.91/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(t70_tops_2, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( l1_pre_topc @ A ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.91/1.14           ( ![C:$i]:
% 0.91/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.91/1.14                 ( m1_subset_1 @
% 0.91/1.14                   C @ 
% 0.91/1.14                   ( k1_zfmisc_1 @
% 0.91/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.91/1.14               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.91/1.14                 ( v3_tops_2 @
% 0.91/1.14                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.91/1.14                   B @ A ) ) ) ) ) ) ))).
% 0.91/1.14  thf('207', plain,
% 0.91/1.14      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.91/1.14         ((v2_struct_0 @ X30)
% 0.91/1.14          | ~ (l1_pre_topc @ X30)
% 0.91/1.14          | ~ (v3_tops_2 @ X31 @ X32 @ X30)
% 0.91/1.14          | (v3_tops_2 @ 
% 0.91/1.14             (k2_tops_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ X31) @ 
% 0.91/1.14             X30 @ X32)
% 0.91/1.14          | ~ (m1_subset_1 @ X31 @ 
% 0.91/1.14               (k1_zfmisc_1 @ 
% 0.91/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 0.91/1.14          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 0.91/1.14          | ~ (v1_funct_1 @ X31)
% 0.91/1.14          | ~ (l1_pre_topc @ X32))),
% 0.91/1.14      inference('cnf', [status(esa)], [t70_tops_2])).
% 0.91/1.14  thf('208', plain,
% 0.91/1.14      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.91/1.14        | (v3_tops_2 @ 
% 0.91/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14           sk_B @ sk_A)
% 0.91/1.14        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.14        | ~ (l1_pre_topc @ sk_B)
% 0.91/1.14        | (v2_struct_0 @ sk_B))),
% 0.91/1.14      inference('sup-', [status(thm)], ['206', '207'])).
% 0.91/1.14  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('211', plain,
% 0.91/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('212', plain, ((l1_pre_topc @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('213', plain,
% 0.91/1.14      (((v3_tops_2 @ 
% 0.91/1.14         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14         sk_B @ sk_A)
% 0.91/1.14        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.14        | (v2_struct_0 @ sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['208', '209', '210', '211', '212'])).
% 0.91/1.14  thf('214', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('215', plain,
% 0.91/1.14      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.14        | (v3_tops_2 @ 
% 0.91/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14           sk_B @ sk_A))),
% 0.91/1.14      inference('clc', [status(thm)], ['213', '214'])).
% 0.91/1.14  thf('216', plain,
% 0.91/1.14      (((v3_tops_2 @ 
% 0.91/1.14         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14         sk_B @ sk_A)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['205', '215'])).
% 0.91/1.14  thf('217', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['43', '45', '47', '49', '167'])).
% 0.91/1.14  thf('218', plain,
% 0.91/1.14      ((v3_tops_2 @ 
% 0.91/1.14        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14        sk_B @ sk_A)),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['216', '217'])).
% 0.91/1.14  thf('219', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((v2_struct_0 @ sk_B)
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.14          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14              (k2_pre_topc @ sk_A @ X0))
% 0.91/1.14              = (k2_pre_topc @ sk_B @ 
% 0.91/1.14                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14                   sk_C) @ 
% 0.91/1.14                  X0))))),
% 0.91/1.14      inference('demod', [status(thm)], ['204', '218'])).
% 0.91/1.14  thf('220', plain, (~ (v2_struct_0 @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('221', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14            (k2_pre_topc @ sk_A @ X0))
% 0.91/1.14            = (k2_pre_topc @ sk_B @ 
% 0.91/1.14               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14                X0)))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('clc', [status(thm)], ['219', '220'])).
% 0.91/1.14  thf('222', plain,
% 0.91/1.14      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14         (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14         = (k2_pre_topc @ sk_B @ 
% 0.91/1.14            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14             sk_D_3)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['194', '221'])).
% 0.91/1.14  thf('223', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.91/1.14         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('224', plain,
% 0.91/1.14      ((![X0 : $i]:
% 0.91/1.14          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14             sk_C @ X0)
% 0.91/1.14             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14                X0))
% 0.91/1.14           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.91/1.14         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['40'])).
% 0.91/1.14  thf('225', plain,
% 0.91/1.14      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14          sk_D_3)
% 0.91/1.14          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14             sk_D_3)))
% 0.91/1.14         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.91/1.14             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['223', '224'])).
% 0.91/1.14  thf('226', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['43', '45', '47', '49', '167'])).
% 0.91/1.14  thf('227', plain,
% 0.91/1.14      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['181', '184', '188', '43', '45', '47', '49', '167', '189'])).
% 0.91/1.14  thf('228', plain,
% 0.91/1.14      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14         sk_D_3)
% 0.91/1.14         = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14            sk_D_3))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['225', '226', '227'])).
% 0.91/1.14  thf('229', plain,
% 0.91/1.14      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.91/1.14         (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14         = (k2_pre_topc @ sk_B @ 
% 0.91/1.14            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14             sk_C @ sk_D_3)))),
% 0.91/1.14      inference('demod', [status(thm)], ['222', '228'])).
% 0.91/1.14  thf('230', plain,
% 0.91/1.14      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14         (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14         = (k2_pre_topc @ sk_B @ 
% 0.91/1.14            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14             sk_C @ sk_D_3)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['191', '229'])).
% 0.91/1.14  thf('231', plain,
% 0.91/1.14      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14          != (k2_pre_topc @ sk_B @ 
% 0.91/1.14              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14               sk_C @ sk_D_3))))
% 0.91/1.14         <= (~
% 0.91/1.14             (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14                sk_C @ (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14                = (k2_pre_topc @ sk_B @ 
% 0.91/1.14                   (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.14                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_3)))))),
% 0.91/1.14      inference('split', [status(esa)], ['165'])).
% 0.91/1.14  thf('232', plain,
% 0.91/1.14      (~
% 0.91/1.14       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14          = (k2_pre_topc @ sk_B @ 
% 0.91/1.14             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14              sk_C @ sk_D_3)))) | 
% 0.91/1.14       ~
% 0.91/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_B))) | 
% 0.91/1.14       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.91/1.14       ~
% 0.91/1.14       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.91/1.14          = (k2_struct_0 @ sk_A))) | 
% 0.91/1.14       ~ ((v2_funct_1 @ sk_C))),
% 0.91/1.14      inference('split', [status(esa)], ['165'])).
% 0.91/1.14  thf('233', plain,
% 0.91/1.14      (~
% 0.91/1.14       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14          = (k2_pre_topc @ sk_B @ 
% 0.91/1.14             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14              sk_C @ sk_D_3))))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)],
% 0.91/1.14                ['43', '45', '47', '49', '167', '188', '184', '181', '232'])).
% 0.91/1.14  thf('234', plain,
% 0.91/1.14      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.91/1.14         (k2_pre_topc @ sk_A @ sk_D_3))
% 0.91/1.14         != (k2_pre_topc @ sk_B @ 
% 0.91/1.14             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.91/1.14              sk_C @ sk_D_3)))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['231', '233'])).
% 0.91/1.14  thf('235', plain, ($false),
% 0.91/1.14      inference('simplify_reflect-', [status(thm)], ['230', '234'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.91/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
