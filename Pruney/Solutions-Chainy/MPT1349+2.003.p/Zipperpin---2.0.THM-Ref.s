%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HtSneOE8wR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:31 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  325 (7498 expanded)
%              Number of leaves         :   39 (2107 expanded)
%              Depth                    :   38
%              Number of atoms          : 6222 (312474 expanded)
%              Number of equality atoms :  235 (12514 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('3',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 )
        = ( k2_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X25 @ X23 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X25 ) @ X23 ) )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X25 )
       != ( k2_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('51',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('52',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 ) )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('55',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('60',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

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

thf('72',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 )
       != ( k2_struct_0 @ X30 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 )
       != ( k2_struct_0 @ X29 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( m1_subset_1 @ ( sk_D_1 @ X31 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_tops_2 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75','81','87','88','89'])).

thf('91',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','90'])).

thf('92',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 ) )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('96',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('101',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ~ ( v2_funct_1 @ sk_C )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('108',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('111',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('116',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','116'])).

thf('118',plain,
    ( ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','106','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('125',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('127',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','22','23','24','27'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ sk_C )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('135',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('136',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('140',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 )
       != ( k2_struct_0 @ X30 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 )
       != ( k2_struct_0 @ X29 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 @ ( k2_pre_topc @ X29 @ ( sk_D_1 @ X31 @ X29 @ X30 ) ) )
       != ( k2_pre_topc @ X30 @ ( k8_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 @ ( sk_D_1 @ X31 @ X29 @ X30 ) ) ) )
      | ( v3_tops_2 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('142',plain,
    ( ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('146',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('147',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('148',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('149',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146','147','148','149','150','151','152'])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','156'])).

thf('158',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
       != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','158'])).

thf('160',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('162',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('163',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('166',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 )
       != ( k2_struct_0 @ X8 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 )
       != ( k2_struct_0 @ X6 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 ) @ X6 @ X8 )
      | ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('172',plain,
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
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,
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
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','177'])).

thf('179',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('180',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('181',plain,(
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

thf('182',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('183',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['183','184','185','186','187','188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('194',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 @ ( k2_pre_topc @ X14 @ ( sk_D @ X13 @ X12 @ X14 ) ) ) @ ( k2_pre_topc @ X12 @ ( k7_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 @ ( sk_D @ X13 @ X12 @ X14 ) ) ) )
      | ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('196',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
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
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('198',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference(demod,[status(thm)],['196','198','199','200','201','202','203','204','205'])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','209'])).

thf('211',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','211'])).

thf('213',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['214'])).

thf('216',plain,
    ( ~ ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X33 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X33 ) ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['213','215'])).

thf('217',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','216'])).

thf('218',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('219',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 )
        = ( k2_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('221',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['221','222','223','224','225'])).

thf('227',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['218','226'])).

thf('228',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['214'])).

thf('229',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('232',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['214'])).

thf('233',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('235',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['214'])).

thf('236',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('239',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['230','233','237','43','45','47','49','216','238'])).

thf('240',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['42','217','239'])).

thf('241',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('242',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['230','233','237','43','45','47','49','216','238'])).

thf('243',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['241','242'])).

thf('244',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('245',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v3_tops_2 @ X31 @ X30 @ X29 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 @ ( k2_pre_topc @ X29 @ X32 ) )
        = ( k2_pre_topc @ X30 @ ( k8_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('246',plain,(
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
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('250',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('251',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['246','247','248','249','250','251','252'])).

thf('254',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('255',plain,(
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

thf('256',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v3_tops_2 @ X27 @ X28 @ X26 )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X27 ) @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_tops_2])).

thf('257',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['257','258','259','260','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['254','264'])).

thf('266',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','216'])).

thf('267',plain,(
    v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['253','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['243','270'])).

thf('272',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('273',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf('274',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','216'])).

thf('276',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['230','233','237','43','45','47','49','216','238'])).

thf('277',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['274','275','276'])).

thf('278',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['271','277'])).

thf('279',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['240','278'])).

thf('280',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
   <= ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['214'])).

thf('281',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['214'])).

thf('282',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
 != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['43','45','47','49','216','237','230','233','281'])).

thf('283',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
 != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['280','282'])).

thf('284',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['279','283'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HtSneOE8wR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.88  % Solved by: fo/fo7.sh
% 0.66/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.88  % done 564 iterations in 0.415s
% 0.66/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.88  % SZS output start Refutation
% 0.66/0.88  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.66/0.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.66/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.66/0.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.66/0.88  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.66/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.88  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.66/0.88  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.66/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.66/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.88  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.66/0.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.66/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.66/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.88  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.66/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.88  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.66/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.66/0.88  thf(t74_tops_2, conjecture,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.88             ( l1_pre_topc @ B ) ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.66/0.88                 ( ( ( k1_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ A ) ) & 
% 0.66/0.88                   ( ( k2_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                   ( v2_funct_1 @ C ) & 
% 0.66/0.88                   ( ![D:$i]:
% 0.66/0.88                     ( ( m1_subset_1 @
% 0.66/0.88                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.88                       ( ( k7_relset_1 @
% 0.66/0.88                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.66/0.88                           ( k2_pre_topc @ A @ D ) ) =
% 0.66/0.88                         ( k2_pre_topc @
% 0.66/0.88                           B @ 
% 0.66/0.88                           ( k7_relset_1 @
% 0.66/0.88                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.88    (~( ![A:$i]:
% 0.66/0.88        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.88          ( ![B:$i]:
% 0.66/0.88            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.88                ( l1_pre_topc @ B ) ) =>
% 0.66/0.88              ( ![C:$i]:
% 0.66/0.88                ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                    ( v1_funct_2 @
% 0.66/0.88                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                    ( m1_subset_1 @
% 0.66/0.88                      C @ 
% 0.66/0.88                      ( k1_zfmisc_1 @
% 0.66/0.88                        ( k2_zfmisc_1 @
% 0.66/0.88                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88                  ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.66/0.88                    ( ( ( k1_relset_1 @
% 0.66/0.88                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                        ( k2_struct_0 @ A ) ) & 
% 0.66/0.88                      ( ( k2_relset_1 @
% 0.66/0.88                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                        ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                      ( v2_funct_1 @ C ) & 
% 0.66/0.88                      ( ![D:$i]:
% 0.66/0.88                        ( ( m1_subset_1 @
% 0.66/0.88                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.88                          ( ( k7_relset_1 @
% 0.66/0.88                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.66/0.88                              ( k2_pre_topc @ A @ D ) ) =
% 0.66/0.88                            ( k2_pre_topc @
% 0.66/0.88                              B @ 
% 0.66/0.88                              ( k7_relset_1 @
% 0.66/0.88                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.66/0.88                                C @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.66/0.88    inference('cnf.neg', [status(esa)], [t74_tops_2])).
% 0.66/0.88  thf('0', plain,
% 0.66/0.88      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_A))
% 0.66/0.88        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('1', plain,
% 0.66/0.88      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.66/0.88         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.88      inference('split', [status(esa)], ['0'])).
% 0.66/0.88  thf(dt_k2_pre_topc, axiom,
% 0.66/0.88    (![A:$i,B:$i]:
% 0.66/0.88     ( ( ( l1_pre_topc @ A ) & 
% 0.66/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.88       ( m1_subset_1 @
% 0.66/0.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.66/0.88  thf('2', plain,
% 0.66/0.88      (![X3 : $i, X4 : $i]:
% 0.66/0.88         (~ (l1_pre_topc @ X3)
% 0.66/0.88          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.66/0.88          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.66/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.66/0.88  thf('3', plain,
% 0.66/0.88      ((((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_2) @ 
% 0.66/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | ~ (l1_pre_topc @ sk_A)))
% 0.66/0.88         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.88  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('5', plain,
% 0.66/0.88      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_2) @ 
% 0.66/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.66/0.88         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.66/0.88  thf('6', plain,
% 0.66/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_A))
% 0.66/0.88        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('7', plain,
% 0.66/0.88      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('split', [status(esa)], ['6'])).
% 0.66/0.88  thf('8', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(d5_tops_2, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( l1_pre_topc @ A ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( l1_pre_topc @ B ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.66/0.88                 ( ( ( k1_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ A ) ) & 
% 0.66/0.88                   ( ( k2_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.66/0.88                   ( v5_pre_topc @
% 0.66/0.88                     ( k2_tops_2 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.66/0.88                     B @ A ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf('9', plain,
% 0.66/0.88      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.88         (~ (l1_pre_topc @ X6)
% 0.66/0.88          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.66/0.88              = (k2_struct_0 @ X6))
% 0.66/0.88          | ~ (m1_subset_1 @ X7 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.66/0.88          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.66/0.88          | ~ (v1_funct_1 @ X7)
% 0.66/0.88          | ~ (l1_pre_topc @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.66/0.88  thf('10', plain,
% 0.66/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            = (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | ~ (l1_pre_topc @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.88  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('13', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('15', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.66/0.88  thf('16', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['7', '15'])).
% 0.66/0.88  thf('17', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(t67_tops_2, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( l1_struct_0 @ A ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( l1_struct_0 @ B ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ![D:$i]:
% 0.66/0.88                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.88                   ( ( ( ( k2_relset_1 @
% 0.66/0.88                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                         ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                       ( v2_funct_1 @ C ) ) =>
% 0.66/0.88                     ( ( k7_relset_1 @
% 0.66/0.88                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.66/0.88                       ( k8_relset_1 @
% 0.66/0.88                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.66/0.88                         ( k2_tops_2 @
% 0.66/0.88                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.66/0.88                         D ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf('18', plain,
% 0.66/0.88      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.66/0.88         (~ (l1_struct_0 @ X22)
% 0.66/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.66/0.88          | ((k7_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ X25 @ 
% 0.66/0.88              X23)
% 0.66/0.88              = (k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24) @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ X25) @ 
% 0.66/0.88                 X23))
% 0.66/0.88          | ~ (v2_funct_1 @ X25)
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ X25)
% 0.66/0.88              != (k2_struct_0 @ X22))
% 0.66/0.88          | ~ (m1_subset_1 @ X25 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 0.66/0.88          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 0.66/0.88          | ~ (v1_funct_1 @ X25)
% 0.66/0.88          | ~ (l1_struct_0 @ X24))),
% 0.66/0.88      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.66/0.88  thf('19', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (~ (l1_struct_0 @ sk_A)
% 0.66/0.88          | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88              != (k2_struct_0 @ sk_B))
% 0.66/0.88          | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88              sk_C @ X0)
% 0.66/0.88              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 X0))
% 0.66/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88          | ~ (l1_struct_0 @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.66/0.88  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(dt_l1_pre_topc, axiom,
% 0.66/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.66/0.88  thf('21', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.66/0.88  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.66/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.88  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('24', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('26', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.66/0.88  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.66/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.66/0.88  thf('28', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88          | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88              sk_C @ X0)
% 0.66/0.88              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 X0))
% 0.66/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.88      inference('demod', [status(thm)], ['19', '22', '23', '24', '27'])).
% 0.66/0.88  thf('29', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ X0)
% 0.66/0.88               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  X0))
% 0.66/0.88           | ~ (v2_funct_1 @ sk_C)))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['16', '28'])).
% 0.66/0.88  thf('30', plain,
% 0.66/0.88      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('split', [status(esa)], ['6'])).
% 0.66/0.88  thf('31', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('32', plain,
% 0.66/0.88      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.88         (~ (l1_pre_topc @ X6)
% 0.66/0.88          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.66/0.88          | (v2_funct_1 @ X7)
% 0.66/0.88          | ~ (m1_subset_1 @ X7 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.66/0.88          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.66/0.88          | ~ (v1_funct_1 @ X7)
% 0.66/0.88          | ~ (l1_pre_topc @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.66/0.88  thf('33', plain,
% 0.66/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (v2_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | ~ (l1_pre_topc @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['31', '32'])).
% 0.66/0.88  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('36', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('38', plain,
% 0.66/0.88      (((v2_funct_1 @ sk_C) | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.66/0.88  thf('39', plain,
% 0.66/0.88      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['30', '38'])).
% 0.66/0.88  thf('40', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ X0)
% 0.66/0.88               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  X0))))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('demod', [status(thm)], ['29', '39'])).
% 0.66/0.88  thf('41', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ X0)
% 0.66/0.88             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88                X0))
% 0.66/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['40'])).
% 0.66/0.88  thf('42', plain,
% 0.66/0.88      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.88          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.88          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             (k2_pre_topc @ sk_A @ sk_D_2))))
% 0.66/0.88         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.66/0.88             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['5', '41'])).
% 0.66/0.88  thf('43', plain,
% 0.66/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_A))) | 
% 0.66/0.88       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('split', [status(esa)], ['6'])).
% 0.66/0.88  thf('44', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B))
% 0.66/0.88        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('45', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B))) | 
% 0.66/0.88       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('split', [status(esa)], ['44'])).
% 0.66/0.88  thf('46', plain, (((v2_funct_1 @ sk_C) | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('47', plain,
% 0.66/0.88      (((v2_funct_1 @ sk_C)) | ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('split', [status(esa)], ['46'])).
% 0.66/0.88  thf('48', plain,
% 0.66/0.88      (![X33 : $i]:
% 0.66/0.88         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88              sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88              = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                 (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C @ X33)))
% 0.66/0.88          | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('49', plain,
% 0.66/0.88      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.66/0.88       (![X33 : $i]:
% 0.66/0.88          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88               = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C @ X33)))))),
% 0.66/0.88      inference('split', [status(esa)], ['48'])).
% 0.66/0.88  thf('50', plain,
% 0.66/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_A)))
% 0.66/0.88         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.66/0.88      inference('split', [status(esa)], ['6'])).
% 0.66/0.88  thf('51', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('split', [status(esa)], ['46'])).
% 0.66/0.88  thf('52', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('split', [status(esa)], ['44'])).
% 0.66/0.88  thf('53', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(t62_tops_2, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( l1_struct_0 @ A ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ( ( ( k2_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                   ( v2_funct_1 @ C ) ) =>
% 0.66/0.88                 ( ( ( k1_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.66/0.88                       ( k2_tops_2 @
% 0.66/0.88                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.66/0.88                     ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                   ( ( k2_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.66/0.88                       ( k2_tops_2 @
% 0.66/0.88                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.66/0.88                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf('54', plain,
% 0.66/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.88         ((v2_struct_0 @ X16)
% 0.66/0.88          | ~ (l1_struct_0 @ X16)
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.66/0.88              != (k2_struct_0 @ X16))
% 0.66/0.88          | ~ (v2_funct_1 @ X18)
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.66/0.88              = (k2_struct_0 @ X17))
% 0.66/0.88          | ~ (m1_subset_1 @ X18 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.66/0.88          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.66/0.88          | ~ (v1_funct_1 @ X18)
% 0.66/0.88          | ~ (l1_struct_0 @ X17))),
% 0.66/0.88      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.66/0.88  thf('55', plain,
% 0.66/0.88      ((~ (l1_struct_0 @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88            = (k2_struct_0 @ sk_A))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (l1_struct_0 @ sk_B)
% 0.66/0.88        | (v2_struct_0 @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.66/0.88  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.66/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.88  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('58', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.66/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.66/0.88  thf('60', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88          = (k2_struct_0 @ sk_A))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | (v2_struct_0 @ sk_B))),
% 0.66/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.66/0.88  thf('61', plain,
% 0.66/0.88      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88         | (v2_struct_0 @ sk_B)
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             = (k2_struct_0 @ sk_A))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['52', '60'])).
% 0.66/0.88  thf('62', plain,
% 0.66/0.88      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88           = (k2_struct_0 @ sk_A))
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | (v2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['61'])).
% 0.66/0.88  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('64', plain,
% 0.66/0.88      (((~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             = (k2_struct_0 @ sk_A))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('clc', [status(thm)], ['62', '63'])).
% 0.66/0.88  thf('65', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88          = (k2_struct_0 @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['51', '64'])).
% 0.66/0.88  thf('66', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(dt_k2_tops_2, axiom,
% 0.66/0.88    (![A:$i,B:$i,C:$i]:
% 0.66/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.88       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.66/0.88         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.66/0.88         ( m1_subset_1 @
% 0.66/0.88           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.66/0.88           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.66/0.88  thf('67', plain,
% 0.66/0.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.88         ((m1_subset_1 @ (k2_tops_2 @ X9 @ X10 @ X11) @ 
% 0.66/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.66/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.66/0.88          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.66/0.88          | ~ (v1_funct_1 @ X11))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.66/0.88  thf('68', plain,
% 0.66/0.88      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (m1_subset_1 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           (k1_zfmisc_1 @ 
% 0.66/0.88            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['66', '67'])).
% 0.66/0.88  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('70', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('71', plain,
% 0.66/0.88      ((m1_subset_1 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.66/0.88      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.66/0.88  thf(t73_tops_2, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.66/0.88                 ( ( ( k1_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ A ) ) & 
% 0.66/0.88                   ( ( k2_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                   ( v2_funct_1 @ C ) & 
% 0.66/0.88                   ( ![D:$i]:
% 0.66/0.88                     ( ( m1_subset_1 @
% 0.66/0.88                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.66/0.88                       ( ( k8_relset_1 @
% 0.66/0.88                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.66/0.88                           ( k2_pre_topc @ B @ D ) ) =
% 0.66/0.88                         ( k2_pre_topc @
% 0.66/0.88                           A @ 
% 0.66/0.88                           ( k8_relset_1 @
% 0.66/0.88                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf('72', plain,
% 0.66/0.88      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.88         (~ (v2_pre_topc @ X29)
% 0.66/0.88          | ~ (l1_pre_topc @ X29)
% 0.66/0.88          | ((k1_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.66/0.88              != (k2_struct_0 @ X30))
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.66/0.88              != (k2_struct_0 @ X29))
% 0.66/0.88          | ~ (v2_funct_1 @ X31)
% 0.66/0.88          | (m1_subset_1 @ (sk_D_1 @ X31 @ X29 @ X30) @ 
% 0.66/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.66/0.88          | (v3_tops_2 @ X31 @ X30 @ X29)
% 0.66/0.88          | ~ (m1_subset_1 @ X31 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.66/0.88          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.66/0.88          | ~ (v1_funct_1 @ X31)
% 0.66/0.88          | ~ (l1_pre_topc @ X30)
% 0.66/0.88          | ~ (v2_pre_topc @ X30)
% 0.66/0.88          | (v2_struct_0 @ X30))),
% 0.66/0.88      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.66/0.88  thf('73', plain,
% 0.66/0.88      (((v2_struct_0 @ sk_B)
% 0.66/0.88        | ~ (v2_pre_topc @ sk_B)
% 0.66/0.88        | ~ (l1_pre_topc @ sk_B)
% 0.66/0.88        | ~ (v1_funct_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88        | ~ (v1_funct_2 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.66/0.88        | (v3_tops_2 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           sk_B @ sk_A)
% 0.66/0.88        | (m1_subset_1 @ 
% 0.66/0.88           (sk_D_1 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_A @ sk_B) @ 
% 0.66/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88        | ~ (v2_funct_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88            != (k2_struct_0 @ sk_A))
% 0.66/0.88        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.66/0.88        | ~ (v2_pre_topc @ sk_A))),
% 0.66/0.88      inference('sup-', [status(thm)], ['71', '72'])).
% 0.66/0.88  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('76', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('77', plain,
% 0.66/0.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.88         ((v1_funct_1 @ (k2_tops_2 @ X9 @ X10 @ X11))
% 0.66/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.66/0.88          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.66/0.88          | ~ (v1_funct_1 @ X11))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.66/0.88  thf('78', plain,
% 0.66/0.88      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (v1_funct_1 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['76', '77'])).
% 0.66/0.88  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('80', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('81', plain,
% 0.66/0.88      ((v1_funct_1 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.66/0.88      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.66/0.88  thf('82', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('83', plain,
% 0.66/0.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.66/0.88         ((v1_funct_2 @ (k2_tops_2 @ X9 @ X10 @ X11) @ X10 @ X9)
% 0.66/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.66/0.88          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.66/0.88          | ~ (v1_funct_1 @ X11))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.66/0.88  thf('84', plain,
% 0.66/0.88      ((~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (v1_funct_2 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['82', '83'])).
% 0.66/0.88  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('86', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('87', plain,
% 0.66/0.88      ((v1_funct_2 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.66/0.88      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.66/0.88  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('90', plain,
% 0.66/0.88      (((v2_struct_0 @ sk_B)
% 0.66/0.88        | (v3_tops_2 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           sk_B @ sk_A)
% 0.66/0.88        | (m1_subset_1 @ 
% 0.66/0.88           (sk_D_1 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_A @ sk_B) @ 
% 0.66/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88        | ~ (v2_funct_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88            != (k2_struct_0 @ sk_A))
% 0.66/0.88        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88            != (k2_struct_0 @ sk_B)))),
% 0.66/0.88      inference('demod', [status(thm)],
% 0.66/0.88                ['73', '74', '75', '81', '87', '88', '89'])).
% 0.66/0.88  thf('91', plain,
% 0.66/0.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.66/0.88         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             != (k2_struct_0 @ sk_B))
% 0.66/0.88         | ~ (v2_funct_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88         | (m1_subset_1 @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B) @ 
% 0.66/0.88            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (v2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['65', '90'])).
% 0.66/0.88  thf('92', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('split', [status(esa)], ['46'])).
% 0.66/0.88  thf('93', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('split', [status(esa)], ['44'])).
% 0.66/0.88  thf('94', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('95', plain,
% 0.66/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.88         ((v2_struct_0 @ X16)
% 0.66/0.88          | ~ (l1_struct_0 @ X16)
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.66/0.88              != (k2_struct_0 @ X16))
% 0.66/0.88          | ~ (v2_funct_1 @ X18)
% 0.66/0.88          | ((k1_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.66/0.88              = (k2_struct_0 @ X16))
% 0.66/0.88          | ~ (m1_subset_1 @ X18 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.66/0.88          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.66/0.88          | ~ (v1_funct_1 @ X18)
% 0.66/0.88          | ~ (l1_struct_0 @ X17))),
% 0.66/0.88      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.66/0.88  thf('96', plain,
% 0.66/0.88      ((~ (l1_struct_0 @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88            = (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (l1_struct_0 @ sk_B)
% 0.66/0.88        | (v2_struct_0 @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['94', '95'])).
% 0.66/0.88  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.66/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.88  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('99', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('100', plain, ((l1_struct_0 @ sk_B)),
% 0.66/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.66/0.88  thf('101', plain,
% 0.66/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88          = (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | (v2_struct_0 @ sk_B))),
% 0.66/0.88      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.66/0.88  thf('102', plain,
% 0.66/0.88      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88         | (v2_struct_0 @ sk_B)
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             = (k2_struct_0 @ sk_B))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['93', '101'])).
% 0.66/0.88  thf('103', plain,
% 0.66/0.88      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88           = (k2_struct_0 @ sk_B))
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | (v2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['102'])).
% 0.66/0.88  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('105', plain,
% 0.66/0.88      (((~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             = (k2_struct_0 @ sk_B))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('clc', [status(thm)], ['103', '104'])).
% 0.66/0.88  thf('106', plain,
% 0.66/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['92', '105'])).
% 0.66/0.88  thf('107', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('split', [status(esa)], ['46'])).
% 0.66/0.88  thf('108', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('split', [status(esa)], ['44'])).
% 0.66/0.88  thf('109', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(t63_tops_2, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( l1_struct_0 @ A ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( l1_struct_0 @ B ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ( ( ( k2_relset_1 @
% 0.66/0.88                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.66/0.88                     ( k2_struct_0 @ B ) ) & 
% 0.66/0.88                   ( v2_funct_1 @ C ) ) =>
% 0.66/0.88                 ( v2_funct_1 @
% 0.66/0.88                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf('110', plain,
% 0.66/0.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.88         (~ (l1_struct_0 @ X19)
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.66/0.88              != (k2_struct_0 @ X19))
% 0.66/0.88          | ~ (v2_funct_1 @ X21)
% 0.66/0.88          | (v2_funct_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.66/0.88          | ~ (m1_subset_1 @ X21 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.66/0.88          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.66/0.88          | ~ (v1_funct_1 @ X21)
% 0.66/0.88          | ~ (l1_struct_0 @ X20))),
% 0.66/0.88      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.66/0.88  thf('111', plain,
% 0.66/0.88      ((~ (l1_struct_0 @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (v2_funct_1 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['109', '110'])).
% 0.66/0.88  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 0.66/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.88  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('114', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('115', plain, ((l1_struct_0 @ sk_B)),
% 0.66/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.66/0.88  thf('116', plain,
% 0.66/0.88      (((v2_funct_1 @ 
% 0.66/0.88         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B)))),
% 0.66/0.88      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 0.66/0.88  thf('117', plain,
% 0.66/0.88      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | (v2_funct_1 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['108', '116'])).
% 0.66/0.88  thf('118', plain,
% 0.66/0.88      ((((v2_funct_1 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['117'])).
% 0.66/0.88  thf('119', plain,
% 0.66/0.88      (((v2_funct_1 @ 
% 0.66/0.88         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['107', '118'])).
% 0.66/0.88  thf('120', plain,
% 0.66/0.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.66/0.88         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88         | (m1_subset_1 @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B) @ 
% 0.66/0.88            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (v2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('demod', [status(thm)], ['91', '106', '119'])).
% 0.66/0.88  thf('121', plain,
% 0.66/0.88      ((((v2_struct_0 @ sk_B)
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (m1_subset_1 @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B) @ 
% 0.66/0.88            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['120'])).
% 0.66/0.88  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('123', plain,
% 0.66/0.88      ((((m1_subset_1 @ 
% 0.66/0.88          (sk_D_1 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           sk_A @ sk_B) @ 
% 0.66/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('clc', [status(thm)], ['121', '122'])).
% 0.66/0.88  thf('124', plain,
% 0.66/0.88      ((![X33 : $i]:
% 0.66/0.88          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88               = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C @ X33)))))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('split', [status(esa)], ['48'])).
% 0.66/0.88  thf('125', plain,
% 0.66/0.88      ((((v3_tops_2 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88          sk_B @ sk_A)
% 0.66/0.88         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ 
% 0.66/0.88             (k2_pre_topc @ sk_A @ 
% 0.66/0.88              (sk_D_1 @ 
% 0.66/0.88               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88               sk_A @ sk_B)))
% 0.66/0.88             = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                 sk_C @ 
% 0.66/0.88                 (sk_D_1 @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  sk_A @ sk_B))))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['123', '124'])).
% 0.66/0.88  thf('126', plain,
% 0.66/0.88      ((((m1_subset_1 @ 
% 0.66/0.88          (sk_D_1 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           sk_A @ sk_B) @ 
% 0.66/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('clc', [status(thm)], ['121', '122'])).
% 0.66/0.88  thf('127', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('split', [status(esa)], ['46'])).
% 0.66/0.88  thf('128', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('split', [status(esa)], ['44'])).
% 0.66/0.88  thf('129', plain,
% 0.66/0.88      (![X0 : $i]:
% 0.66/0.88         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88          | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88              sk_C @ X0)
% 0.66/0.88              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 X0))
% 0.66/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.88      inference('demod', [status(thm)], ['19', '22', '23', '24', '27'])).
% 0.66/0.88  thf('130', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ X0)
% 0.66/0.88               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  X0))
% 0.66/0.88           | ~ (v2_funct_1 @ sk_C)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['128', '129'])).
% 0.66/0.88  thf('131', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (~ (v2_funct_1 @ sk_C)
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ X0)
% 0.66/0.88               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  X0))
% 0.66/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['130'])).
% 0.66/0.88  thf('132', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ X0)
% 0.66/0.88               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  X0))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['127', '131'])).
% 0.66/0.88  thf('133', plain,
% 0.66/0.88      ((((v3_tops_2 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88          sk_B @ sk_A)
% 0.66/0.88         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ 
% 0.66/0.88             (sk_D_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88              sk_A @ sk_B))
% 0.66/0.88             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88                (sk_D_1 @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 sk_A @ sk_B)))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['126', '132'])).
% 0.66/0.88  thf('134', plain,
% 0.66/0.88      ((((m1_subset_1 @ 
% 0.66/0.88          (sk_D_1 @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           sk_A @ sk_B) @ 
% 0.66/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('clc', [status(thm)], ['121', '122'])).
% 0.66/0.88  thf('135', plain,
% 0.66/0.88      (![X3 : $i, X4 : $i]:
% 0.66/0.88         (~ (l1_pre_topc @ X3)
% 0.66/0.88          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.66/0.88          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.66/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.66/0.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.66/0.88  thf('136', plain,
% 0.66/0.88      ((((v3_tops_2 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88          sk_B @ sk_A)
% 0.66/0.88         | (m1_subset_1 @ 
% 0.66/0.88            (k2_pre_topc @ sk_A @ 
% 0.66/0.88             (sk_D_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88              sk_A @ sk_B)) @ 
% 0.66/0.88            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88         | ~ (l1_pre_topc @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['134', '135'])).
% 0.66/0.88  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('138', plain,
% 0.66/0.88      ((((v3_tops_2 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88          sk_B @ sk_A)
% 0.66/0.88         | (m1_subset_1 @ 
% 0.66/0.88            (k2_pre_topc @ sk_A @ 
% 0.66/0.88             (sk_D_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88              sk_A @ sk_B)) @ 
% 0.66/0.88            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('demod', [status(thm)], ['136', '137'])).
% 0.66/0.88  thf('139', plain,
% 0.66/0.88      ((![X0 : $i]:
% 0.66/0.88          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ X0)
% 0.66/0.88               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  X0))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['127', '131'])).
% 0.66/0.88  thf('140', plain,
% 0.66/0.88      ((((v3_tops_2 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88          sk_B @ sk_A)
% 0.66/0.88         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ 
% 0.66/0.88             (k2_pre_topc @ sk_A @ 
% 0.66/0.88              (sk_D_1 @ 
% 0.66/0.88               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88               sk_A @ sk_B)))
% 0.66/0.88             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88                (k2_pre_topc @ sk_A @ 
% 0.66/0.88                 (sk_D_1 @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  sk_A @ sk_B))))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['138', '139'])).
% 0.66/0.88  thf('141', plain,
% 0.66/0.88      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.88         (~ (v2_pre_topc @ X29)
% 0.66/0.88          | ~ (l1_pre_topc @ X29)
% 0.66/0.88          | ((k1_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.66/0.88              != (k2_struct_0 @ X30))
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.66/0.88              != (k2_struct_0 @ X29))
% 0.66/0.88          | ~ (v2_funct_1 @ X31)
% 0.66/0.88          | ((k8_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31 @ 
% 0.66/0.88              (k2_pre_topc @ X29 @ (sk_D_1 @ X31 @ X29 @ X30)))
% 0.66/0.88              != (k2_pre_topc @ X30 @ 
% 0.66/0.88                  (k8_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ 
% 0.66/0.88                   X31 @ (sk_D_1 @ X31 @ X29 @ X30))))
% 0.66/0.88          | (v3_tops_2 @ X31 @ X30 @ X29)
% 0.66/0.88          | ~ (m1_subset_1 @ X31 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.66/0.88          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.66/0.88          | ~ (v1_funct_1 @ X31)
% 0.66/0.88          | ~ (l1_pre_topc @ X30)
% 0.66/0.88          | ~ (v2_pre_topc @ X30)
% 0.66/0.88          | (v2_struct_0 @ X30))),
% 0.66/0.88      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.66/0.88  thf('142', plain,
% 0.66/0.88      (((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.88           (k2_pre_topc @ sk_A @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B)))
% 0.66/0.88           != (k2_pre_topc @ sk_B @ 
% 0.66/0.88               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88                (sk_D_1 @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 sk_A @ sk_B))))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (v2_struct_0 @ sk_B)
% 0.66/0.88         | ~ (v2_pre_topc @ sk_B)
% 0.66/0.88         | ~ (l1_pre_topc @ sk_B)
% 0.66/0.88         | ~ (v1_funct_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88         | ~ (v1_funct_2 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.66/0.88         | ~ (m1_subset_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88              (k1_zfmisc_1 @ 
% 0.66/0.88               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | ~ (v2_funct_1 @ 
% 0.66/0.88              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88         | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             != (k2_struct_0 @ sk_A))
% 0.66/0.88         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88             != (k2_struct_0 @ sk_B))
% 0.66/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.66/0.88         | ~ (v2_pre_topc @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['140', '141'])).
% 0.66/0.88  thf('143', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('144', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('145', plain,
% 0.66/0.88      ((v1_funct_1 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.66/0.88      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.66/0.88  thf('146', plain,
% 0.66/0.88      ((v1_funct_2 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.66/0.88      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.66/0.88  thf('147', plain,
% 0.66/0.88      ((m1_subset_1 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.66/0.88      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.66/0.88  thf('148', plain,
% 0.66/0.88      (((v2_funct_1 @ 
% 0.66/0.88         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['107', '118'])).
% 0.66/0.88  thf('149', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88          = (k2_struct_0 @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['51', '64'])).
% 0.66/0.88  thf('150', plain,
% 0.66/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['92', '105'])).
% 0.66/0.88  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('153', plain,
% 0.66/0.88      (((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.88           (k2_pre_topc @ sk_A @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B)))
% 0.66/0.88           != (k2_pre_topc @ sk_B @ 
% 0.66/0.88               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88                (sk_D_1 @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 sk_A @ sk_B))))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (v2_struct_0 @ sk_B)
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.66/0.88         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('demod', [status(thm)],
% 0.66/0.88                ['142', '143', '144', '145', '146', '147', '148', '149', 
% 0.66/0.88                 '150', '151', '152'])).
% 0.66/0.88  thf('154', plain,
% 0.66/0.88      ((((v2_struct_0 @ sk_B)
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ 
% 0.66/0.88             (k2_pre_topc @ sk_A @ 
% 0.66/0.88              (sk_D_1 @ 
% 0.66/0.88               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88               sk_A @ sk_B)))
% 0.66/0.88             != (k2_pre_topc @ sk_B @ 
% 0.66/0.88                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C) @ 
% 0.66/0.88                  (sk_D_1 @ 
% 0.66/0.88                   (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                    sk_C) @ 
% 0.66/0.88                   sk_A @ sk_B))))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['153'])).
% 0.66/0.88  thf('155', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('156', plain,
% 0.66/0.88      (((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.88           (k2_pre_topc @ sk_A @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B)))
% 0.66/0.88           != (k2_pre_topc @ sk_B @ 
% 0.66/0.88               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88                (sk_D_1 @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 sk_A @ sk_B))))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('clc', [status(thm)], ['154', '155'])).
% 0.66/0.88  thf('157', plain,
% 0.66/0.88      (((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.88           (k2_pre_topc @ sk_A @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B)))
% 0.66/0.88           != (k2_pre_topc @ sk_B @ 
% 0.66/0.88               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C @ 
% 0.66/0.88                (sk_D_1 @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 sk_A @ sk_B))))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('sup-', [status(thm)], ['133', '156'])).
% 0.66/0.88  thf('158', plain,
% 0.66/0.88      ((((v3_tops_2 @ 
% 0.66/0.88          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88          sk_B @ sk_A)
% 0.66/0.88         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ 
% 0.66/0.88             (k2_pre_topc @ sk_A @ 
% 0.66/0.88              (sk_D_1 @ 
% 0.66/0.88               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88               sk_A @ sk_B)))
% 0.66/0.88             != (k2_pre_topc @ sk_B @ 
% 0.66/0.88                 (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C @ 
% 0.66/0.88                  (sk_D_1 @ 
% 0.66/0.88                   (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                    sk_C) @ 
% 0.66/0.88                   sk_A @ sk_B))))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('simplify', [status(thm)], ['157'])).
% 0.66/0.88  thf('159', plain,
% 0.66/0.88      (((((k2_pre_topc @ sk_B @ 
% 0.66/0.88           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.88            (sk_D_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_A @ sk_B)))
% 0.66/0.88           != (k2_pre_topc @ sk_B @ 
% 0.66/0.88               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C @ 
% 0.66/0.88                (sk_D_1 @ 
% 0.66/0.88                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                  sk_C) @ 
% 0.66/0.88                 sk_A @ sk_B))))
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)
% 0.66/0.88         | (v3_tops_2 @ 
% 0.66/0.88            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88            sk_B @ sk_A)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['125', '158'])).
% 0.66/0.88  thf('160', plain,
% 0.66/0.88      (((v3_tops_2 @ 
% 0.66/0.88         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88         sk_B @ sk_A))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['159'])).
% 0.66/0.88  thf('161', plain,
% 0.66/0.88      ((m1_subset_1 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.66/0.88      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.66/0.88  thf('162', plain,
% 0.66/0.88      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.88         (~ (l1_pre_topc @ X6)
% 0.66/0.88          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.66/0.88          | (v5_pre_topc @ X7 @ X8 @ X6)
% 0.66/0.88          | ~ (m1_subset_1 @ X7 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.66/0.88          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.66/0.88          | ~ (v1_funct_1 @ X7)
% 0.66/0.88          | ~ (l1_pre_topc @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.66/0.88  thf('163', plain,
% 0.66/0.88      ((~ (l1_pre_topc @ sk_B)
% 0.66/0.88        | ~ (v1_funct_1 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.88        | ~ (v1_funct_2 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.66/0.88        | (v5_pre_topc @ 
% 0.66/0.88           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88           sk_B @ sk_A)
% 0.66/0.88        | ~ (v3_tops_2 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_B @ sk_A)
% 0.66/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.66/0.88      inference('sup-', [status(thm)], ['161', '162'])).
% 0.66/0.88  thf('164', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('165', plain,
% 0.66/0.88      ((v1_funct_1 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.66/0.88      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.66/0.88  thf('166', plain,
% 0.66/0.88      ((v1_funct_2 @ 
% 0.66/0.88        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.66/0.88      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.66/0.88  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('168', plain,
% 0.66/0.88      (((v5_pre_topc @ 
% 0.66/0.88         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88         sk_B @ sk_A)
% 0.66/0.88        | ~ (v3_tops_2 @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_B @ sk_A))),
% 0.66/0.88      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 0.66/0.88  thf('169', plain,
% 0.66/0.88      (((v5_pre_topc @ 
% 0.66/0.88         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88         sk_B @ sk_A))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['160', '168'])).
% 0.66/0.88  thf('170', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('171', plain,
% 0.66/0.88      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.88         (~ (l1_pre_topc @ X6)
% 0.66/0.88          | ((k1_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.66/0.88              != (k2_struct_0 @ X8))
% 0.66/0.88          | ((k2_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.66/0.88              != (k2_struct_0 @ X6))
% 0.66/0.88          | ~ (v2_funct_1 @ X7)
% 0.66/0.88          | ~ (v5_pre_topc @ X7 @ X8 @ X6)
% 0.66/0.88          | ~ (v5_pre_topc @ 
% 0.66/0.88               (k2_tops_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7) @ 
% 0.66/0.88               X6 @ X8)
% 0.66/0.88          | (v3_tops_2 @ X7 @ X8 @ X6)
% 0.66/0.88          | ~ (m1_subset_1 @ X7 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.66/0.88          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.66/0.88          | ~ (v1_funct_1 @ X7)
% 0.66/0.88          | ~ (l1_pre_topc @ X8))),
% 0.66/0.88      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.66/0.88  thf('172', plain,
% 0.66/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | ~ (v5_pre_topc @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_B @ sk_A)
% 0.66/0.88        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_A))
% 0.66/0.88        | ~ (l1_pre_topc @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['170', '171'])).
% 0.66/0.88  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('175', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('176', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('177', plain,
% 0.66/0.88      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | ~ (v5_pre_topc @ 
% 0.66/0.88             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.88             sk_B @ sk_A)
% 0.66/0.88        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_B))
% 0.66/0.88        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88            != (k2_struct_0 @ sk_A)))),
% 0.66/0.88      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 0.66/0.88  thf('178', plain,
% 0.66/0.88      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88           != (k2_struct_0 @ sk_A))
% 0.66/0.88         | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88             != (k2_struct_0 @ sk_B))
% 0.66/0.88         | ~ (v2_funct_1 @ sk_C)
% 0.66/0.88         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['169', '177'])).
% 0.66/0.88  thf('179', plain,
% 0.66/0.88      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88          = (k2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.88      inference('split', [status(esa)], ['44'])).
% 0.66/0.88  thf('180', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.66/0.88      inference('split', [status(esa)], ['46'])).
% 0.66/0.88  thf('181', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf(t57_tops_2, axiom,
% 0.66/0.88    (![A:$i]:
% 0.66/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.88       ( ![B:$i]:
% 0.66/0.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.88             ( l1_pre_topc @ B ) ) =>
% 0.66/0.88           ( ![C:$i]:
% 0.66/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.88                 ( m1_subset_1 @
% 0.66/0.88                   C @ 
% 0.66/0.88                   ( k1_zfmisc_1 @
% 0.66/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.88               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.66/0.88                 ( ![D:$i]:
% 0.66/0.88                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.88                     ( r1_tarski @
% 0.66/0.88                       ( k7_relset_1 @
% 0.66/0.88                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.66/0.88                         ( k2_pre_topc @ A @ D ) ) @ 
% 0.66/0.88                       ( k2_pre_topc @
% 0.66/0.88                         B @ 
% 0.66/0.88                         ( k7_relset_1 @
% 0.66/0.88                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.88  thf('182', plain,
% 0.66/0.88      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.88         ((v2_struct_0 @ X12)
% 0.66/0.88          | ~ (v2_pre_topc @ X12)
% 0.66/0.88          | ~ (l1_pre_topc @ X12)
% 0.66/0.88          | (m1_subset_1 @ (sk_D @ X13 @ X12 @ X14) @ 
% 0.66/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.66/0.88          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.66/0.88          | ~ (m1_subset_1 @ X13 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.66/0.88          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.66/0.88          | ~ (v1_funct_1 @ X13)
% 0.66/0.88          | ~ (l1_pre_topc @ X14)
% 0.66/0.88          | ~ (v2_pre_topc @ X14))),
% 0.66/0.88      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.66/0.88  thf('183', plain,
% 0.66/0.88      ((~ (v2_pre_topc @ sk_A)
% 0.66/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.66/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.66/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88        | ~ (l1_pre_topc @ sk_B)
% 0.66/0.88        | ~ (v2_pre_topc @ sk_B)
% 0.66/0.88        | (v2_struct_0 @ sk_B))),
% 0.66/0.88      inference('sup-', [status(thm)], ['181', '182'])).
% 0.66/0.88  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('187', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('188', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('189', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('190', plain,
% 0.66/0.88      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.66/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88        | (v2_struct_0 @ sk_B))),
% 0.66/0.88      inference('demod', [status(thm)],
% 0.66/0.88                ['183', '184', '185', '186', '187', '188', '189'])).
% 0.66/0.88  thf('191', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('192', plain,
% 0.66/0.88      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.66/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.66/0.88      inference('clc', [status(thm)], ['190', '191'])).
% 0.66/0.88  thf('193', plain,
% 0.66/0.88      ((![X33 : $i]:
% 0.66/0.88          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88               sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88               = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                   sk_C @ X33)))))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('split', [status(esa)], ['48'])).
% 0.66/0.88  thf('194', plain,
% 0.66/0.88      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88             sk_C @ (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.66/0.88             = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                 sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['192', '193'])).
% 0.66/0.88  thf('195', plain,
% 0.66/0.88      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.88         ((v2_struct_0 @ X12)
% 0.66/0.88          | ~ (v2_pre_topc @ X12)
% 0.66/0.88          | ~ (l1_pre_topc @ X12)
% 0.66/0.88          | ~ (r1_tarski @ 
% 0.66/0.88               (k7_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 0.66/0.88                X13 @ (k2_pre_topc @ X14 @ (sk_D @ X13 @ X12 @ X14))) @ 
% 0.66/0.88               (k2_pre_topc @ X12 @ 
% 0.66/0.88                (k7_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 0.66/0.88                 X13 @ (sk_D @ X13 @ X12 @ X14))))
% 0.66/0.88          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.66/0.88          | ~ (m1_subset_1 @ X13 @ 
% 0.66/0.88               (k1_zfmisc_1 @ 
% 0.66/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.66/0.88          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.66/0.88          | ~ (v1_funct_1 @ X13)
% 0.66/0.88          | ~ (l1_pre_topc @ X14)
% 0.66/0.88          | ~ (v2_pre_topc @ X14))),
% 0.66/0.88      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.66/0.88  thf('196', plain,
% 0.66/0.88      (((~ (r1_tarski @ 
% 0.66/0.88            (k2_pre_topc @ sk_B @ 
% 0.66/0.88             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.66/0.88            (k2_pre_topc @ sk_B @ 
% 0.66/0.88             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.66/0.88         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | ~ (v2_pre_topc @ sk_A)
% 0.66/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.66/0.88         | ~ (v1_funct_1 @ sk_C)
% 0.66/0.88         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.88         | ~ (m1_subset_1 @ sk_C @ 
% 0.66/0.88              (k1_zfmisc_1 @ 
% 0.66/0.88               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.66/0.88         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | ~ (l1_pre_topc @ sk_B)
% 0.66/0.88         | ~ (v2_pre_topc @ sk_B)
% 0.66/0.88         | (v2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('sup-', [status(thm)], ['194', '195'])).
% 0.66/0.88  thf(d10_xboole_0, axiom,
% 0.66/0.88    (![A:$i,B:$i]:
% 0.66/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.88  thf('197', plain,
% 0.66/0.88      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.66/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.88  thf('198', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.66/0.88      inference('simplify', [status(thm)], ['197'])).
% 0.66/0.88  thf('199', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('200', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('202', plain,
% 0.66/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('203', plain,
% 0.66/0.88      ((m1_subset_1 @ sk_C @ 
% 0.66/0.88        (k1_zfmisc_1 @ 
% 0.66/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('204', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('205', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('206', plain,
% 0.66/0.88      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | (v2_struct_0 @ sk_B)))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('demod', [status(thm)],
% 0.66/0.88                ['196', '198', '199', '200', '201', '202', '203', '204', '205'])).
% 0.66/0.88  thf('207', plain,
% 0.66/0.88      ((((v2_struct_0 @ sk_B) | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['206'])).
% 0.66/0.88  thf('208', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.88  thf('209', plain,
% 0.66/0.88      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.66/0.88         <= ((![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('clc', [status(thm)], ['207', '208'])).
% 0.66/0.88  thf('210', plain,
% 0.66/0.88      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88           != (k2_struct_0 @ sk_A))
% 0.66/0.88         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.66/0.88         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('demod', [status(thm)], ['178', '179', '180', '209'])).
% 0.66/0.88  thf('211', plain,
% 0.66/0.88      ((((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.88         | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.88             != (k2_struct_0 @ sk_A))))
% 0.66/0.88         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.88             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.88             (![X33 : $i]:
% 0.66/0.88                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.88                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.88                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.88                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.88                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.88      inference('simplify', [status(thm)], ['210'])).
% 0.66/0.88  thf('212', plain,
% 0.66/0.88      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.66/0.88         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.66/0.88         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.88                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.66/0.88             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.89             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.89             (![X33 : $i]:
% 0.66/0.89                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.89                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.89                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['50', '211'])).
% 0.66/0.89  thf('213', plain,
% 0.66/0.89      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.66/0.89         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.66/0.89             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.89             ((v2_funct_1 @ sk_C)) & 
% 0.66/0.89             (![X33 : $i]:
% 0.66/0.89                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.89                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.89                     = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                         (u1_struct_0 @ sk_B) @ sk_C @ X33))))))),
% 0.66/0.89      inference('simplify', [status(thm)], ['212'])).
% 0.66/0.89  thf('214', plain,
% 0.66/0.89      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89          != (k2_pre_topc @ sk_B @ 
% 0.66/0.89              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89               sk_C @ sk_D_2)))
% 0.66/0.89        | ~ (v2_funct_1 @ sk_C)
% 0.66/0.89        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89            != (k2_struct_0 @ sk_B))
% 0.66/0.89        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89            != (k2_struct_0 @ sk_A))
% 0.66/0.89        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('215', plain,
% 0.66/0.89      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.66/0.89         <= (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('split', [status(esa)], ['214'])).
% 0.66/0.89  thf('216', plain,
% 0.66/0.89      (~
% 0.66/0.89       (![X33 : $i]:
% 0.66/0.89          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.89           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89               sk_C @ (k2_pre_topc @ sk_A @ X33))
% 0.66/0.89               = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                   sk_C @ X33))))) | 
% 0.66/0.89       ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.66/0.89       ~
% 0.66/0.89       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_B))) | 
% 0.66/0.89       ~
% 0.66/0.89       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_A))) | 
% 0.66/0.89       ~ ((v2_funct_1 @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['213', '215'])).
% 0.66/0.89  thf('217', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['43', '45', '47', '49', '216'])).
% 0.66/0.89  thf('218', plain,
% 0.66/0.89      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.66/0.89         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('split', [status(esa)], ['6'])).
% 0.66/0.89  thf('219', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ 
% 0.66/0.89        (k1_zfmisc_1 @ 
% 0.66/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('220', plain,
% 0.66/0.89      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.89         (~ (l1_pre_topc @ X6)
% 0.66/0.89          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.66/0.89          | ((k1_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.66/0.89              = (k2_struct_0 @ X8))
% 0.66/0.89          | ~ (m1_subset_1 @ X7 @ 
% 0.66/0.89               (k1_zfmisc_1 @ 
% 0.66/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.66/0.89          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.66/0.89          | ~ (v1_funct_1 @ X7)
% 0.66/0.89          | ~ (l1_pre_topc @ X8))),
% 0.66/0.89      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.66/0.89  thf('221', plain,
% 0.66/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.89        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89            = (k2_struct_0 @ sk_A))
% 0.66/0.89        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.89        | ~ (l1_pre_topc @ sk_B))),
% 0.66/0.89      inference('sup-', [status(thm)], ['219', '220'])).
% 0.66/0.89  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('224', plain,
% 0.66/0.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('225', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('226', plain,
% 0.66/0.89      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_A))
% 0.66/0.89        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('demod', [status(thm)], ['221', '222', '223', '224', '225'])).
% 0.66/0.89  thf('227', plain,
% 0.66/0.89      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_A)))
% 0.66/0.89         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['218', '226'])).
% 0.66/0.89  thf('228', plain,
% 0.66/0.89      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          != (k2_struct_0 @ sk_A)))
% 0.66/0.89         <= (~
% 0.66/0.89             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.66/0.89      inference('split', [status(esa)], ['214'])).
% 0.66/0.89  thf('229', plain,
% 0.66/0.89      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.66/0.89         <= (~
% 0.66/0.89             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.66/0.89             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['227', '228'])).
% 0.66/0.89  thf('230', plain,
% 0.66/0.89      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_A))) | 
% 0.66/0.89       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('simplify', [status(thm)], ['229'])).
% 0.66/0.89  thf('231', plain,
% 0.66/0.89      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['30', '38'])).
% 0.66/0.89  thf('232', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.66/0.89      inference('split', [status(esa)], ['214'])).
% 0.66/0.89  thf('233', plain,
% 0.66/0.89      (((v2_funct_1 @ sk_C)) | ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('sup-', [status(thm)], ['231', '232'])).
% 0.66/0.89  thf('234', plain,
% 0.66/0.89      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_B)))
% 0.66/0.89         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['7', '15'])).
% 0.66/0.89  thf('235', plain,
% 0.66/0.89      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          != (k2_struct_0 @ sk_B)))
% 0.66/0.89         <= (~
% 0.66/0.89             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.66/0.89      inference('split', [status(esa)], ['214'])).
% 0.66/0.89  thf('236', plain,
% 0.66/0.89      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.66/0.89         <= (~
% 0.66/0.89             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.66/0.89             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['234', '235'])).
% 0.66/0.89  thf('237', plain,
% 0.66/0.89      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_B))) | 
% 0.66/0.89       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('simplify', [status(thm)], ['236'])).
% 0.66/0.89  thf('238', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.66/0.89       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.66/0.89       ~
% 0.66/0.89       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_B))) | 
% 0.66/0.89       ~ ((v2_funct_1 @ sk_C)) | 
% 0.66/0.89       ~
% 0.66/0.89       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_A)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('239', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['230', '233', '237', '43', '45', '47', '49', '216', '238'])).
% 0.66/0.89  thf('240', plain,
% 0.66/0.89      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89         (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89         = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89            (k2_pre_topc @ sk_A @ sk_D_2)))),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['42', '217', '239'])).
% 0.66/0.89  thf('241', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.66/0.89         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('242', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['230', '233', '237', '43', '45', '47', '49', '216', '238'])).
% 0.66/0.89  thf('243', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['241', '242'])).
% 0.66/0.89  thf('244', plain,
% 0.66/0.89      ((m1_subset_1 @ 
% 0.66/0.89        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89        (k1_zfmisc_1 @ 
% 0.66/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.66/0.89      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.66/0.89  thf('245', plain,
% 0.66/0.89      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.66/0.89         (~ (v2_pre_topc @ X29)
% 0.66/0.89          | ~ (l1_pre_topc @ X29)
% 0.66/0.89          | ~ (v3_tops_2 @ X31 @ X30 @ X29)
% 0.66/0.89          | ((k8_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31 @ 
% 0.66/0.89              (k2_pre_topc @ X29 @ X32))
% 0.66/0.89              = (k2_pre_topc @ X30 @ 
% 0.66/0.89                 (k8_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ 
% 0.66/0.89                  X31 @ X32)))
% 0.66/0.89          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.66/0.89          | ~ (m1_subset_1 @ X31 @ 
% 0.66/0.89               (k1_zfmisc_1 @ 
% 0.66/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.66/0.89          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.66/0.89          | ~ (v1_funct_1 @ X31)
% 0.66/0.89          | ~ (l1_pre_topc @ X30)
% 0.66/0.89          | ~ (v2_pre_topc @ X30)
% 0.66/0.89          | (v2_struct_0 @ X30))),
% 0.66/0.89      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.66/0.89  thf('246', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((v2_struct_0 @ sk_B)
% 0.66/0.89          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.89          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.89          | ~ (v1_funct_1 @ 
% 0.66/0.89               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.66/0.89          | ~ (v1_funct_2 @ 
% 0.66/0.89               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.89          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89              (k2_pre_topc @ sk_A @ X0))
% 0.66/0.89              = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                   sk_C) @ 
% 0.66/0.89                  X0)))
% 0.66/0.89          | ~ (v3_tops_2 @ 
% 0.66/0.89               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89               sk_B @ sk_A)
% 0.66/0.89          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.89          | ~ (v2_pre_topc @ sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['244', '245'])).
% 0.66/0.89  thf('247', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('248', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('249', plain,
% 0.66/0.89      ((v1_funct_1 @ 
% 0.66/0.89        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.66/0.89      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.66/0.89  thf('250', plain,
% 0.66/0.89      ((v1_funct_2 @ 
% 0.66/0.89        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.66/0.89  thf('251', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('252', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('253', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((v2_struct_0 @ sk_B)
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.89          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89              (k2_pre_topc @ sk_A @ X0))
% 0.66/0.89              = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                   sk_C) @ 
% 0.66/0.89                  X0)))
% 0.66/0.89          | ~ (v3_tops_2 @ 
% 0.66/0.89               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89               sk_B @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)],
% 0.66/0.89                ['246', '247', '248', '249', '250', '251', '252'])).
% 0.66/0.89  thf('254', plain,
% 0.66/0.89      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.66/0.89         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('split', [status(esa)], ['6'])).
% 0.66/0.89  thf('255', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ 
% 0.66/0.89        (k1_zfmisc_1 @ 
% 0.66/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(t70_tops_2, axiom,
% 0.66/0.89    (![A:$i]:
% 0.66/0.89     ( ( l1_pre_topc @ A ) =>
% 0.66/0.89       ( ![B:$i]:
% 0.66/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.66/0.89           ( ![C:$i]:
% 0.66/0.89             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.89                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.89                 ( m1_subset_1 @
% 0.66/0.89                   C @ 
% 0.66/0.89                   ( k1_zfmisc_1 @
% 0.66/0.89                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.89               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.66/0.89                 ( v3_tops_2 @
% 0.66/0.89                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.66/0.89                   B @ A ) ) ) ) ) ) ))).
% 0.66/0.89  thf('256', plain,
% 0.66/0.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.66/0.89         ((v2_struct_0 @ X26)
% 0.66/0.89          | ~ (l1_pre_topc @ X26)
% 0.66/0.89          | ~ (v3_tops_2 @ X27 @ X28 @ X26)
% 0.66/0.89          | (v3_tops_2 @ 
% 0.66/0.89             (k2_tops_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ X27) @ 
% 0.66/0.89             X26 @ X28)
% 0.66/0.89          | ~ (m1_subset_1 @ X27 @ 
% 0.66/0.89               (k1_zfmisc_1 @ 
% 0.66/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 0.66/0.89          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 0.66/0.89          | ~ (v1_funct_1 @ X27)
% 0.66/0.89          | ~ (l1_pre_topc @ X28))),
% 0.66/0.89      inference('cnf', [status(esa)], [t70_tops_2])).
% 0.66/0.89  thf('257', plain,
% 0.66/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.89        | (v3_tops_2 @ 
% 0.66/0.89           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89           sk_B @ sk_A)
% 0.66/0.89        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.89        | ~ (l1_pre_topc @ sk_B)
% 0.66/0.89        | (v2_struct_0 @ sk_B))),
% 0.66/0.89      inference('sup-', [status(thm)], ['255', '256'])).
% 0.66/0.89  thf('258', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('259', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('260', plain,
% 0.66/0.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('261', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('262', plain,
% 0.66/0.89      (((v3_tops_2 @ 
% 0.66/0.89         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89         sk_B @ sk_A)
% 0.66/0.89        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.89        | (v2_struct_0 @ sk_B))),
% 0.66/0.89      inference('demod', [status(thm)], ['257', '258', '259', '260', '261'])).
% 0.66/0.89  thf('263', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('264', plain,
% 0.66/0.89      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.89        | (v3_tops_2 @ 
% 0.66/0.89           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89           sk_B @ sk_A))),
% 0.66/0.89      inference('clc', [status(thm)], ['262', '263'])).
% 0.66/0.89  thf('265', plain,
% 0.66/0.89      (((v3_tops_2 @ 
% 0.66/0.89         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89         sk_B @ sk_A)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['254', '264'])).
% 0.66/0.89  thf('266', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['43', '45', '47', '49', '216'])).
% 0.66/0.89  thf('267', plain,
% 0.66/0.89      ((v3_tops_2 @ 
% 0.66/0.89        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89        sk_B @ sk_A)),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['265', '266'])).
% 0.66/0.89  thf('268', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((v2_struct_0 @ sk_B)
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.89          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89              (k2_pre_topc @ sk_A @ X0))
% 0.66/0.89              = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                   sk_C) @ 
% 0.66/0.89                  X0))))),
% 0.66/0.89      inference('demod', [status(thm)], ['253', '267'])).
% 0.66/0.89  thf('269', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('270', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89            (k2_pre_topc @ sk_A @ X0))
% 0.66/0.89            = (k2_pre_topc @ sk_B @ 
% 0.66/0.89               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89                X0)))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.89      inference('clc', [status(thm)], ['268', '269'])).
% 0.66/0.89  thf('271', plain,
% 0.66/0.89      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89         (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89         = (k2_pre_topc @ sk_B @ 
% 0.66/0.89            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89             sk_D_2)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['243', '270'])).
% 0.66/0.89  thf('272', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.66/0.89         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('273', plain,
% 0.66/0.89      ((![X0 : $i]:
% 0.66/0.89          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89             sk_C @ X0)
% 0.66/0.89             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89                X0))
% 0.66/0.89           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.66/0.89         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.66/0.89      inference('simplify', [status(thm)], ['40'])).
% 0.66/0.89  thf('274', plain,
% 0.66/0.89      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89          sk_D_2)
% 0.66/0.89          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89             sk_D_2)))
% 0.66/0.89         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.66/0.89             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['272', '273'])).
% 0.66/0.89  thf('275', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['43', '45', '47', '49', '216'])).
% 0.66/0.89  thf('276', plain,
% 0.66/0.89      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['230', '233', '237', '43', '45', '47', '49', '216', '238'])).
% 0.66/0.89  thf('277', plain,
% 0.66/0.89      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89         sk_D_2)
% 0.66/0.89         = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89            sk_D_2))),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['274', '275', '276'])).
% 0.66/0.89  thf('278', plain,
% 0.66/0.89      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.66/0.89         (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89         = (k2_pre_topc @ sk_B @ 
% 0.66/0.89            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89             sk_C @ sk_D_2)))),
% 0.66/0.89      inference('demod', [status(thm)], ['271', '277'])).
% 0.66/0.89  thf('279', plain,
% 0.66/0.89      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89         (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89         = (k2_pre_topc @ sk_B @ 
% 0.66/0.89            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89             sk_C @ sk_D_2)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['240', '278'])).
% 0.66/0.89  thf('280', plain,
% 0.66/0.89      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89          != (k2_pre_topc @ sk_B @ 
% 0.66/0.89              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89               sk_C @ sk_D_2))))
% 0.66/0.89         <= (~
% 0.66/0.89             (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89                sk_C @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89                = (k2_pre_topc @ sk_B @ 
% 0.66/0.89                   (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.89                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_2)))))),
% 0.66/0.89      inference('split', [status(esa)], ['214'])).
% 0.66/0.89  thf('281', plain,
% 0.66/0.89      (~
% 0.66/0.89       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89          = (k2_pre_topc @ sk_B @ 
% 0.66/0.89             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89              sk_C @ sk_D_2)))) | 
% 0.66/0.89       ~
% 0.66/0.89       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_B))) | 
% 0.66/0.89       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.66/0.89       ~
% 0.66/0.89       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.66/0.89          = (k2_struct_0 @ sk_A))) | 
% 0.66/0.89       ~ ((v2_funct_1 @ sk_C))),
% 0.66/0.89      inference('split', [status(esa)], ['214'])).
% 0.66/0.89  thf('282', plain,
% 0.66/0.89      (~
% 0.66/0.89       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89          = (k2_pre_topc @ sk_B @ 
% 0.66/0.89             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89              sk_C @ sk_D_2))))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)],
% 0.66/0.89                ['43', '45', '47', '49', '216', '237', '230', '233', '281'])).
% 0.66/0.89  thf('283', plain,
% 0.66/0.89      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.66/0.89         (k2_pre_topc @ sk_A @ sk_D_2))
% 0.66/0.89         != (k2_pre_topc @ sk_B @ 
% 0.66/0.89             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.89              sk_C @ sk_D_2)))),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['280', '282'])).
% 0.66/0.89  thf('284', plain, ($false),
% 0.66/0.89      inference('simplify_reflect-', [status(thm)], ['279', '283'])).
% 0.66/0.89  
% 0.66/0.89  % SZS output end Refutation
% 0.66/0.89  
% 0.66/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
