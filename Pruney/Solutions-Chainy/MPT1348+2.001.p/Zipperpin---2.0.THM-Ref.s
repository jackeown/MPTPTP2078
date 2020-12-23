%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xsttiXQFWt

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:30 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  288 (4853 expanded)
%              Number of leaves         :   36 (1396 expanded)
%              Depth                    :   30
%              Number of atoms          : 5105 (212210 expanded)
%              Number of equality atoms :  140 (7791 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t73_tops_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                          = ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_2])).

thf('0',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( r1_tarski @ ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ( r1_tarski @ ( k2_pre_topc @ X14 @ ( k8_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 @ X15 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 @ ( k2_pre_topc @ X12 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X0 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X0 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19','20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X0 ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
        = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

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

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( m1_subset_1 @ ( sk_D_1 @ X17 @ X16 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v5_pre_topc @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','48','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('61',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('64',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t68_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ X21 )
        = ( k7_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 ) @ X21 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 )
       != ( k2_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t68_tops_2])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('73',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['71','74','75','76','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ sk_C )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('84',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('87',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 @ ( k2_pre_topc @ X18 @ ( sk_D_1 @ X17 @ X16 @ X18 ) ) ) @ ( k2_pre_topc @ X16 @ ( k7_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 @ ( sk_D_1 @ X17 @ X16 @ X18 ) ) ) )
      | ( v5_pre_topc @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('89',plain,
    ( ( ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('93',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95','96'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ~ ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','100'])).

thf('102',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['61','102'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['103','105'])).

thf('107',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
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

thf('110',plain,
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
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
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
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['107','115'])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('118',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('121',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126','127'])).

thf('129',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('130',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X14 @ ( k8_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 @ ( sk_D @ X13 @ X12 @ X14 ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 @ ( k2_pre_topc @ X12 @ ( sk_D @ X13 @ X12 @ X14 ) ) ) )
      | ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_2])).

thf('132',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139','140'])).

thf('142',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
          = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','142'])).

thf('144',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','144'])).

thf('146',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['147'])).

thf('149',plain,
    ( ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
          | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X24 ) )
            = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X24 ) ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['146','148'])).

thf('150',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','27','29','31','149'])).

thf('151',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
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

thf('154',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['154','155','156','157','158'])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['151','159'])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['147'])).

thf('162',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('167',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['164','172'])).

thf('174',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['147'])).

thf('175',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
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

thf('179',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','181','182','183'])).

thf('185',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['147'])).

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
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('190',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['163','175','188','25','27','29','31','149','189'])).

thf('191',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['24','150','190'])).

thf('192',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('193',plain,
    ( ~ ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
   <= ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['147'])).

thf('195',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['147'])).

thf('196',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
 != ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['25','27','29','31','149','188','163','175','195'])).

thf('197',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
 != ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['194','196'])).

thf('198',plain,(
    ~ ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['193','197'])).

thf('199',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('200',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['163','175','188','25','27','29','31','149','189'])).

thf('201',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['199','200'])).

thf('202',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('203',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v5_pre_topc @ X17 @ X18 @ X16 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 @ ( k2_pre_topc @ X18 @ X19 ) ) @ ( k2_pre_topc @ X16 @ ( k7_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('208',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['204','205','206','207','208','209','210'])).

thf('212',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 ) @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('215',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['215','216','217','218','219'])).

thf('221',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['212','220'])).

thf('222',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','27','29','31','149'])).

thf('223',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['201','226'])).

thf('228',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('229',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('230',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['71','74','75','76','79'])).

thf('235',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['164','172'])).

thf('237',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['232','238'])).

thf('240',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','27','29','31','149'])).

thf('241',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['163','175','188','25','27','29','31','149','189'])).

thf('242',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) )
    = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('244',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['237'])).

thf('245',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','27','29','31','149'])).

thf('247',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['163','175','188','25','27','29','31','149','189'])).

thf('248',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 )
    = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['245','246','247'])).

thf('249',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['227','242','248'])).

thf('250',plain,(
    $false ),
    inference(demod,[status(thm)],['198','249'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xsttiXQFWt
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.65/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.83  % Solved by: fo/fo7.sh
% 0.65/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.83  % done 423 iterations in 0.376s
% 0.65/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.83  % SZS output start Refutation
% 0.65/0.83  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.65/0.83  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.65/0.83  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.65/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.65/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.65/0.83  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.65/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.83  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.65/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.65/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.65/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.65/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.65/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.65/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.83  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.65/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.65/0.83  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.65/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.65/0.83  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.65/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.65/0.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.65/0.83  thf(t73_tops_2, conjecture,
% 0.65/0.83    (![A:$i]:
% 0.65/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.83       ( ![B:$i]:
% 0.65/0.83         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.65/0.83           ( ![C:$i]:
% 0.65/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.65/0.83                 ( m1_subset_1 @
% 0.65/0.83                   C @ 
% 0.65/0.83                   ( k1_zfmisc_1 @
% 0.65/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.65/0.83               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.65/0.83                 ( ( ( k1_relset_1 @
% 0.65/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                     ( k2_struct_0 @ A ) ) & 
% 0.65/0.83                   ( ( k2_relset_1 @
% 0.65/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                     ( k2_struct_0 @ B ) ) & 
% 0.65/0.83                   ( v2_funct_1 @ C ) & 
% 0.65/0.83                   ( ![D:$i]:
% 0.65/0.83                     ( ( m1_subset_1 @
% 0.65/0.83                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.65/0.83                       ( ( k8_relset_1 @
% 0.65/0.83                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.65/0.83                           ( k2_pre_topc @ B @ D ) ) =
% 0.65/0.83                         ( k2_pre_topc @
% 0.65/0.83                           A @ 
% 0.65/0.83                           ( k8_relset_1 @
% 0.65/0.83                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.65/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.83    (~( ![A:$i]:
% 0.65/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.65/0.83            ( l1_pre_topc @ A ) ) =>
% 0.65/0.83          ( ![B:$i]:
% 0.65/0.83            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.65/0.83              ( ![C:$i]:
% 0.65/0.83                ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.83                    ( v1_funct_2 @
% 0.65/0.83                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.65/0.83                    ( m1_subset_1 @
% 0.65/0.83                      C @ 
% 0.65/0.83                      ( k1_zfmisc_1 @
% 0.65/0.83                        ( k2_zfmisc_1 @
% 0.65/0.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.65/0.83                  ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.65/0.83                    ( ( ( k1_relset_1 @
% 0.65/0.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                        ( k2_struct_0 @ A ) ) & 
% 0.65/0.83                      ( ( k2_relset_1 @
% 0.65/0.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                        ( k2_struct_0 @ B ) ) & 
% 0.65/0.83                      ( v2_funct_1 @ C ) & 
% 0.65/0.83                      ( ![D:$i]:
% 0.65/0.83                        ( ( m1_subset_1 @
% 0.65/0.83                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.65/0.83                          ( ( k8_relset_1 @
% 0.65/0.83                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.65/0.83                              ( k2_pre_topc @ B @ D ) ) =
% 0.65/0.83                            ( k2_pre_topc @
% 0.65/0.83                              A @ 
% 0.65/0.83                              ( k8_relset_1 @
% 0.65/0.83                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.65/0.83                                C @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.65/0.83    inference('cnf.neg', [status(esa)], [t73_tops_2])).
% 0.65/0.83  thf('0', plain,
% 0.65/0.83      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_B))
% 0.65/0.83        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_A))
% 0.65/0.83        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('1', plain,
% 0.65/0.83      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.65/0.83         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.83      inference('split', [status(esa)], ['0'])).
% 0.65/0.83  thf('2', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A))
% 0.65/0.83        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('3', plain,
% 0.65/0.83      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('split', [status(esa)], ['2'])).
% 0.65/0.83  thf('4', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(d5_tops_2, axiom,
% 0.65/0.83    (![A:$i]:
% 0.65/0.83     ( ( l1_pre_topc @ A ) =>
% 0.65/0.83       ( ![B:$i]:
% 0.65/0.83         ( ( l1_pre_topc @ B ) =>
% 0.65/0.83           ( ![C:$i]:
% 0.65/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.65/0.83                 ( m1_subset_1 @
% 0.65/0.83                   C @ 
% 0.65/0.83                   ( k1_zfmisc_1 @
% 0.65/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.65/0.83               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.65/0.83                 ( ( ( k1_relset_1 @
% 0.65/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                     ( k2_struct_0 @ A ) ) & 
% 0.65/0.83                   ( ( k2_relset_1 @
% 0.65/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                     ( k2_struct_0 @ B ) ) & 
% 0.65/0.83                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.65/0.83                   ( v5_pre_topc @
% 0.65/0.83                     ( k2_tops_2 @
% 0.65/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.65/0.83                     B @ A ) ) ) ) ) ) ) ))).
% 0.65/0.83  thf('5', plain,
% 0.65/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.83         (~ (l1_pre_topc @ X6)
% 0.65/0.83          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.65/0.83          | (v5_pre_topc @ X7 @ X8 @ X6)
% 0.65/0.83          | ~ (m1_subset_1 @ X7 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.65/0.83          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.65/0.83          | ~ (v1_funct_1 @ X7)
% 0.65/0.83          | ~ (l1_pre_topc @ X8))),
% 0.65/0.83      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.65/0.83  thf('6', plain,
% 0.65/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.65/0.83  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('9', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('11', plain,
% 0.65/0.83      (((v5_pre_topc @ sk_C @ sk_A @ sk_B) | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.65/0.83  thf('12', plain,
% 0.65/0.83      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['3', '11'])).
% 0.65/0.83  thf('13', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(t56_tops_2, axiom,
% 0.65/0.83    (![A:$i]:
% 0.65/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.83       ( ![B:$i]:
% 0.65/0.83         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.65/0.83           ( ![C:$i]:
% 0.65/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.65/0.83                 ( m1_subset_1 @
% 0.65/0.83                   C @ 
% 0.65/0.83                   ( k1_zfmisc_1 @
% 0.65/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.65/0.83               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.65/0.83                 ( ![D:$i]:
% 0.65/0.83                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.65/0.83                     ( r1_tarski @
% 0.65/0.83                       ( k2_pre_topc @
% 0.65/0.83                         A @ 
% 0.65/0.83                         ( k8_relset_1 @
% 0.65/0.83                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 0.65/0.83                       ( k8_relset_1 @
% 0.65/0.83                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.65/0.83                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.65/0.83  thf('14', plain,
% 0.65/0.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.65/0.83         (~ (v2_pre_topc @ X12)
% 0.65/0.83          | ~ (l1_pre_topc @ X12)
% 0.65/0.83          | ~ (v5_pre_topc @ X13 @ X14 @ X12)
% 0.65/0.83          | (r1_tarski @ 
% 0.65/0.83             (k2_pre_topc @ X14 @ 
% 0.65/0.83              (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13 @ 
% 0.65/0.83               X15)) @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13 @ 
% 0.65/0.83              (k2_pre_topc @ X12 @ X15)))
% 0.65/0.83          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.83          | ~ (m1_subset_1 @ X13 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.65/0.83          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.65/0.83          | ~ (v1_funct_1 @ X13)
% 0.65/0.83          | ~ (l1_pre_topc @ X14)
% 0.65/0.83          | ~ (v2_pre_topc @ X14))),
% 0.65/0.83      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.65/0.83  thf('15', plain,
% 0.65/0.83      (![X0 : $i]:
% 0.65/0.83         (~ (v2_pre_topc @ sk_A)
% 0.65/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.65/0.83          | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83          | (r1_tarski @ 
% 0.65/0.83             (k2_pre_topc @ sk_A @ 
% 0.65/0.83              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ X0)) @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ (k2_pre_topc @ sk_B @ X0)))
% 0.65/0.83          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.65/0.83          | ~ (v2_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.65/0.83  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('19', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('22', plain,
% 0.65/0.83      (![X0 : $i]:
% 0.65/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83          | (r1_tarski @ 
% 0.65/0.83             (k2_pre_topc @ sk_A @ 
% 0.65/0.83              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ X0)) @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ (k2_pre_topc @ sk_B @ X0)))
% 0.65/0.83          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('demod', [status(thm)],
% 0.65/0.83                ['15', '16', '17', '18', '19', '20', '21'])).
% 0.65/0.83  thf('23', plain,
% 0.65/0.83      ((![X0 : $i]:
% 0.65/0.83          ((r1_tarski @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ X0)) @ 
% 0.65/0.83            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83             sk_C @ (k2_pre_topc @ sk_B @ X0)))
% 0.65/0.83           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['12', '22'])).
% 0.65/0.83  thf('24', plain,
% 0.65/0.83      (((r1_tarski @ 
% 0.65/0.83         (k2_pre_topc @ sk_A @ 
% 0.65/0.83          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.83           sk_D_2)) @ 
% 0.65/0.83         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.83          (k2_pre_topc @ sk_B @ sk_D_2))))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.65/0.83             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['1', '23'])).
% 0.65/0.83  thf('25', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A))) | 
% 0.65/0.83       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('split', [status(esa)], ['2'])).
% 0.65/0.83  thf('26', plain,
% 0.65/0.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_B))
% 0.65/0.83        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('27', plain,
% 0.65/0.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_B))) | 
% 0.65/0.83       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('split', [status(esa)], ['26'])).
% 0.65/0.83  thf('28', plain, (((v2_funct_1 @ sk_C) | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('29', plain,
% 0.65/0.83      (((v2_funct_1 @ sk_C)) | ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('split', [status(esa)], ['28'])).
% 0.65/0.83  thf('30', plain,
% 0.65/0.83      (![X24 : $i]:
% 0.65/0.83         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83              = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                 (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C @ X24)))
% 0.65/0.83          | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('31', plain,
% 0.65/0.83      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.65/0.83       (![X24 : $i]:
% 0.65/0.83          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83               = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                  (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C @ X24)))))),
% 0.65/0.83      inference('split', [status(esa)], ['30'])).
% 0.65/0.83  thf('32', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A)))
% 0.65/0.83         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.65/0.83      inference('split', [status(esa)], ['2'])).
% 0.65/0.83  thf('33', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(dt_k2_tops_2, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i]:
% 0.65/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.65/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.83       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.65/0.83         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.65/0.83         ( m1_subset_1 @
% 0.65/0.83           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.65/0.83           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.65/0.83  thf('34', plain,
% 0.65/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.65/0.83         ((m1_subset_1 @ (k2_tops_2 @ X9 @ X10 @ X11) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.65/0.83          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.65/0.83          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.65/0.83          | ~ (v1_funct_1 @ X11))),
% 0.65/0.83      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.65/0.83  thf('35', plain,
% 0.65/0.83      ((~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (m1_subset_1 @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83           (k1_zfmisc_1 @ 
% 0.65/0.83            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['33', '34'])).
% 0.65/0.83  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('37', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('38', plain,
% 0.65/0.83      ((m1_subset_1 @ 
% 0.65/0.83        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.65/0.83      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.65/0.83  thf(t57_tops_2, axiom,
% 0.65/0.83    (![A:$i]:
% 0.65/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.65/0.83       ( ![B:$i]:
% 0.65/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.65/0.83             ( l1_pre_topc @ B ) ) =>
% 0.65/0.83           ( ![C:$i]:
% 0.65/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.65/0.83                 ( m1_subset_1 @
% 0.65/0.83                   C @ 
% 0.65/0.83                   ( k1_zfmisc_1 @
% 0.65/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.65/0.83               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.65/0.83                 ( ![D:$i]:
% 0.65/0.83                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.83                     ( r1_tarski @
% 0.65/0.83                       ( k7_relset_1 @
% 0.65/0.83                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.65/0.83                         ( k2_pre_topc @ A @ D ) ) @ 
% 0.65/0.83                       ( k2_pre_topc @
% 0.65/0.83                         B @ 
% 0.65/0.83                         ( k7_relset_1 @
% 0.65/0.83                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.65/0.83  thf('39', plain,
% 0.65/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.83         ((v2_struct_0 @ X16)
% 0.65/0.83          | ~ (v2_pre_topc @ X16)
% 0.65/0.83          | ~ (l1_pre_topc @ X16)
% 0.65/0.83          | (m1_subset_1 @ (sk_D_1 @ X17 @ X16 @ X18) @ 
% 0.65/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.65/0.83          | (v5_pre_topc @ X17 @ X18 @ X16)
% 0.65/0.83          | ~ (m1_subset_1 @ X17 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.65/0.83          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.65/0.83          | ~ (v1_funct_1 @ X17)
% 0.65/0.83          | ~ (l1_pre_topc @ X18)
% 0.65/0.83          | ~ (v2_pre_topc @ X18))),
% 0.65/0.83      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.65/0.83  thf('40', plain,
% 0.65/0.83      ((~ (v2_pre_topc @ sk_B)
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B)
% 0.65/0.83        | ~ (v1_funct_1 @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.65/0.83        | ~ (v1_funct_2 @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.65/0.83        | (v5_pre_topc @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83           sk_B @ sk_A)
% 0.65/0.83        | (m1_subset_1 @ 
% 0.65/0.83           (sk_D_1 @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_A @ sk_B) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.65/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.65/0.83        | (v2_struct_0 @ sk_A))),
% 0.65/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.65/0.83  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('43', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('44', plain,
% 0.65/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.65/0.83         ((v1_funct_1 @ (k2_tops_2 @ X9 @ X10 @ X11))
% 0.65/0.83          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.65/0.83          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.65/0.83          | ~ (v1_funct_1 @ X11))),
% 0.65/0.83      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.65/0.83  thf('45', plain,
% 0.65/0.83      ((~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (v1_funct_1 @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['43', '44'])).
% 0.65/0.83  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('47', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('48', plain,
% 0.65/0.83      ((v1_funct_1 @ 
% 0.65/0.83        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.65/0.83      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.65/0.83  thf('49', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('50', plain,
% 0.65/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.65/0.83         ((v1_funct_2 @ (k2_tops_2 @ X9 @ X10 @ X11) @ X10 @ X9)
% 0.65/0.83          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.65/0.83          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.65/0.83          | ~ (v1_funct_1 @ X11))),
% 0.65/0.83      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.65/0.83  thf('51', plain,
% 0.65/0.83      ((~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (v1_funct_2 @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['49', '50'])).
% 0.65/0.83  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('53', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('54', plain,
% 0.65/0.83      ((v1_funct_2 @ 
% 0.65/0.83        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.65/0.83      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.65/0.83  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('57', plain,
% 0.65/0.83      (((v5_pre_topc @ 
% 0.65/0.83         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83         sk_B @ sk_A)
% 0.65/0.83        | (m1_subset_1 @ 
% 0.65/0.83           (sk_D_1 @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_A @ sk_B) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | (v2_struct_0 @ sk_A))),
% 0.65/0.83      inference('demod', [status(thm)],
% 0.65/0.83                ['40', '41', '42', '48', '54', '55', '56'])).
% 0.65/0.83  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('59', plain,
% 0.65/0.83      (((m1_subset_1 @ 
% 0.65/0.83         (sk_D_1 @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_A @ sk_B) @ 
% 0.65/0.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | (v5_pre_topc @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83           sk_B @ sk_A))),
% 0.65/0.83      inference('clc', [status(thm)], ['57', '58'])).
% 0.65/0.83  thf('60', plain,
% 0.65/0.83      ((![X24 : $i]:
% 0.65/0.83          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83               = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                  (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C @ X24)))))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('split', [status(esa)], ['30'])).
% 0.65/0.83  thf('61', plain,
% 0.65/0.83      ((((v5_pre_topc @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_B @ sk_A)
% 0.65/0.83         | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83             sk_C @ 
% 0.65/0.83             (k2_pre_topc @ sk_B @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B)))
% 0.65/0.83             = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                 sk_C @ 
% 0.65/0.83                 (sk_D_1 @ 
% 0.65/0.83                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C) @ 
% 0.65/0.83                  sk_A @ sk_B))))))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['59', '60'])).
% 0.65/0.83  thf('62', plain,
% 0.65/0.83      (((m1_subset_1 @ 
% 0.65/0.83         (sk_D_1 @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_A @ sk_B) @ 
% 0.65/0.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | (v5_pre_topc @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83           sk_B @ sk_A))),
% 0.65/0.83      inference('clc', [status(thm)], ['57', '58'])).
% 0.65/0.83  thf(dt_k2_pre_topc, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( ( l1_pre_topc @ A ) & 
% 0.65/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.65/0.83       ( m1_subset_1 @
% 0.65/0.83         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.65/0.83  thf('63', plain,
% 0.65/0.83      (![X3 : $i, X4 : $i]:
% 0.65/0.83         (~ (l1_pre_topc @ X3)
% 0.65/0.83          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.65/0.83          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.65/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.65/0.83      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.65/0.83  thf('64', plain,
% 0.65/0.83      (((v5_pre_topc @ 
% 0.65/0.83         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83         sk_B @ sk_A)
% 0.65/0.83        | (m1_subset_1 @ 
% 0.65/0.83           (k2_pre_topc @ sk_B @ 
% 0.65/0.83            (sk_D_1 @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             sk_A @ sk_B)) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['62', '63'])).
% 0.65/0.83  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('66', plain,
% 0.65/0.83      (((v5_pre_topc @ 
% 0.65/0.83         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83         sk_B @ sk_A)
% 0.65/0.83        | (m1_subset_1 @ 
% 0.65/0.83           (k2_pre_topc @ sk_B @ 
% 0.65/0.83            (sk_D_1 @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             sk_A @ sk_B)) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('demod', [status(thm)], ['64', '65'])).
% 0.65/0.83  thf('67', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('split', [status(esa)], ['28'])).
% 0.65/0.83  thf('68', plain,
% 0.65/0.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_B)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.65/0.83      inference('split', [status(esa)], ['26'])).
% 0.65/0.83  thf('69', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(t68_tops_2, axiom,
% 0.65/0.83    (![A:$i]:
% 0.65/0.83     ( ( l1_struct_0 @ A ) =>
% 0.65/0.83       ( ![B:$i]:
% 0.65/0.83         ( ( l1_struct_0 @ B ) =>
% 0.65/0.83           ( ![C:$i]:
% 0.65/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.65/0.83                 ( m1_subset_1 @
% 0.65/0.83                   C @ 
% 0.65/0.83                   ( k1_zfmisc_1 @
% 0.65/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.65/0.83               ( ![D:$i]:
% 0.65/0.83                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.65/0.83                   ( ( ( ( k2_relset_1 @
% 0.65/0.83                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.65/0.83                         ( k2_struct_0 @ B ) ) & 
% 0.65/0.83                       ( v2_funct_1 @ C ) ) =>
% 0.65/0.83                     ( ( k8_relset_1 @
% 0.65/0.83                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.65/0.83                       ( k7_relset_1 @
% 0.65/0.83                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.65/0.83                         ( k2_tops_2 @
% 0.65/0.83                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.65/0.83                         D ) ) ) ) ) ) ) ) ) ))).
% 0.65/0.83  thf('70', plain,
% 0.65/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.83         (~ (l1_struct_0 @ X20)
% 0.65/0.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.65/0.83          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23 @ 
% 0.65/0.83              X21)
% 0.65/0.83              = (k7_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22) @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23) @ 
% 0.65/0.83                 X21))
% 0.65/0.83          | ~ (v2_funct_1 @ X23)
% 0.65/0.83          | ((k2_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23)
% 0.65/0.83              != (k2_struct_0 @ X20))
% 0.65/0.83          | ~ (m1_subset_1 @ X23 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.65/0.83          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.65/0.83          | ~ (v1_funct_1 @ X23)
% 0.65/0.83          | ~ (l1_struct_0 @ X22))),
% 0.65/0.83      inference('cnf', [status(esa)], [t68_tops_2])).
% 0.65/0.83  thf('71', plain,
% 0.65/0.83      (![X0 : $i]:
% 0.65/0.83         (~ (l1_struct_0 @ sk_A)
% 0.65/0.83          | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83              != (k2_struct_0 @ sk_B))
% 0.65/0.83          | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ X0)
% 0.65/0.83              = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 X0))
% 0.65/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83          | ~ (l1_struct_0 @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['69', '70'])).
% 0.65/0.83  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(dt_l1_pre_topc, axiom,
% 0.65/0.83    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.65/0.83  thf('73', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.65/0.83      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.65/0.83  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.65/0.83      inference('sup-', [status(thm)], ['72', '73'])).
% 0.65/0.83  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('76', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('78', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.65/0.83      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.65/0.83  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.65/0.83      inference('sup-', [status(thm)], ['77', '78'])).
% 0.65/0.83  thf('80', plain,
% 0.65/0.83      (![X0 : $i]:
% 0.65/0.83         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_B))
% 0.65/0.83          | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ X0)
% 0.65/0.83              = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 X0))
% 0.65/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('demod', [status(thm)], ['71', '74', '75', '76', '79'])).
% 0.65/0.83  thf('81', plain,
% 0.65/0.83      ((![X0 : $i]:
% 0.65/0.83          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.65/0.83           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ X0)
% 0.65/0.83               = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C) @ 
% 0.65/0.83                  X0))
% 0.65/0.83           | ~ (v2_funct_1 @ sk_C)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['68', '80'])).
% 0.65/0.83  thf('82', plain,
% 0.65/0.83      ((![X0 : $i]:
% 0.65/0.83          (~ (v2_funct_1 @ sk_C)
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ X0)
% 0.65/0.83               = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C) @ 
% 0.65/0.83                  X0))
% 0.65/0.83           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.65/0.83      inference('simplify', [status(thm)], ['81'])).
% 0.65/0.83  thf('83', plain,
% 0.65/0.83      ((![X0 : $i]:
% 0.65/0.83          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ X0)
% 0.65/0.83               = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C) @ 
% 0.65/0.83                  X0))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['67', '82'])).
% 0.65/0.83  thf('84', plain,
% 0.65/0.83      ((((v5_pre_topc @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_B @ sk_A)
% 0.65/0.83         | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83             sk_C @ 
% 0.65/0.83             (k2_pre_topc @ sk_B @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B)))
% 0.65/0.83             = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83                (k2_pre_topc @ sk_B @ 
% 0.65/0.83                 (sk_D_1 @ 
% 0.65/0.83                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C) @ 
% 0.65/0.83                  sk_A @ sk_B))))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['66', '83'])).
% 0.65/0.83  thf('85', plain,
% 0.65/0.83      (((m1_subset_1 @ 
% 0.65/0.83         (sk_D_1 @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_A @ sk_B) @ 
% 0.65/0.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | (v5_pre_topc @ 
% 0.65/0.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83           sk_B @ sk_A))),
% 0.65/0.83      inference('clc', [status(thm)], ['57', '58'])).
% 0.65/0.83  thf('86', plain,
% 0.65/0.83      ((![X0 : $i]:
% 0.65/0.83          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ X0)
% 0.65/0.83               = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C) @ 
% 0.65/0.83                  X0))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['67', '82'])).
% 0.65/0.83  thf('87', plain,
% 0.65/0.83      ((((v5_pre_topc @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_B @ sk_A)
% 0.65/0.83         | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83             sk_C @ 
% 0.65/0.83             (sk_D_1 @ 
% 0.65/0.83              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83              sk_A @ sk_B))
% 0.65/0.83             = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83                (sk_D_1 @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 sk_A @ sk_B)))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['85', '86'])).
% 0.65/0.83  thf('88', plain,
% 0.65/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.83         ((v2_struct_0 @ X16)
% 0.65/0.83          | ~ (v2_pre_topc @ X16)
% 0.65/0.83          | ~ (l1_pre_topc @ X16)
% 0.65/0.83          | ~ (r1_tarski @ 
% 0.65/0.83               (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ 
% 0.65/0.83                X17 @ (k2_pre_topc @ X18 @ (sk_D_1 @ X17 @ X16 @ X18))) @ 
% 0.65/0.83               (k2_pre_topc @ X16 @ 
% 0.65/0.83                (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ 
% 0.65/0.83                 X17 @ (sk_D_1 @ X17 @ X16 @ X18))))
% 0.65/0.83          | (v5_pre_topc @ X17 @ X18 @ X16)
% 0.65/0.83          | ~ (m1_subset_1 @ X17 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.65/0.83          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.65/0.83          | ~ (v1_funct_1 @ X17)
% 0.65/0.83          | ~ (l1_pre_topc @ X18)
% 0.65/0.83          | ~ (v2_pre_topc @ X18))),
% 0.65/0.83      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.65/0.83  thf('89', plain,
% 0.65/0.83      (((~ (r1_tarski @ 
% 0.65/0.83            (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             (k2_pre_topc @ sk_B @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))) @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))))
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | ~ (v2_pre_topc @ sk_B)
% 0.65/0.83         | ~ (l1_pre_topc @ sk_B)
% 0.65/0.83         | ~ (v1_funct_1 @ 
% 0.65/0.83              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.65/0.83         | ~ (v1_funct_2 @ 
% 0.65/0.83              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.65/0.83         | ~ (m1_subset_1 @ 
% 0.65/0.83              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83              (k1_zfmisc_1 @ 
% 0.65/0.83               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | ~ (l1_pre_topc @ sk_A)
% 0.65/0.83         | ~ (v2_pre_topc @ sk_A)
% 0.65/0.83         | (v2_struct_0 @ sk_A)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['87', '88'])).
% 0.65/0.83  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('92', plain,
% 0.65/0.83      ((v1_funct_1 @ 
% 0.65/0.83        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.65/0.83      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.65/0.83  thf('93', plain,
% 0.65/0.83      ((v1_funct_2 @ 
% 0.65/0.83        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.65/0.83      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.65/0.83  thf('94', plain,
% 0.65/0.83      ((m1_subset_1 @ 
% 0.65/0.83        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.65/0.83      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.65/0.83  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('97', plain,
% 0.65/0.83      (((~ (r1_tarski @ 
% 0.65/0.83            (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             (k2_pre_topc @ sk_B @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))) @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))))
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | (v2_struct_0 @ sk_A)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('demod', [status(thm)],
% 0.65/0.83                ['89', '90', '91', '92', '93', '94', '95', '96'])).
% 0.65/0.83  thf('98', plain,
% 0.65/0.83      ((((v2_struct_0 @ sk_A)
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | ~ (r1_tarski @ 
% 0.65/0.83              (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               (k2_pre_topc @ sk_B @ 
% 0.65/0.83                (sk_D_1 @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 sk_A @ sk_B))) @ 
% 0.65/0.83              (k2_pre_topc @ sk_A @ 
% 0.65/0.83               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C @ 
% 0.65/0.83                (sk_D_1 @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 sk_A @ sk_B))))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('simplify', [status(thm)], ['97'])).
% 0.65/0.83  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('100', plain,
% 0.65/0.83      (((~ (r1_tarski @ 
% 0.65/0.83            (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             (k2_pre_topc @ sk_B @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))) @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))))
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('clc', [status(thm)], ['98', '99'])).
% 0.65/0.83  thf('101', plain,
% 0.65/0.83      (((~ (r1_tarski @ 
% 0.65/0.83            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83             sk_C @ 
% 0.65/0.83             (k2_pre_topc @ sk_B @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))) @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))))
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['84', '100'])).
% 0.65/0.83  thf('102', plain,
% 0.65/0.83      ((((v5_pre_topc @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_B @ sk_A)
% 0.65/0.83         | ~ (r1_tarski @ 
% 0.65/0.83              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ 
% 0.65/0.83               (k2_pre_topc @ sk_B @ 
% 0.65/0.83                (sk_D_1 @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 sk_A @ sk_B))) @ 
% 0.65/0.83              (k2_pre_topc @ sk_A @ 
% 0.65/0.83               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C @ 
% 0.65/0.83                (sk_D_1 @ 
% 0.65/0.83                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                  sk_C) @ 
% 0.65/0.83                 sk_A @ sk_B))))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('simplify', [status(thm)], ['101'])).
% 0.65/0.83  thf('103', plain,
% 0.65/0.83      (((~ (r1_tarski @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))) @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ 
% 0.65/0.83              (sk_D_1 @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83               sk_A @ sk_B))))
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['61', '102'])).
% 0.65/0.83  thf(d10_xboole_0, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.65/0.83  thf('104', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.65/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.65/0.83  thf('105', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.65/0.83      inference('simplify', [status(thm)], ['104'])).
% 0.65/0.83  thf('106', plain,
% 0.65/0.83      ((((v5_pre_topc @ 
% 0.65/0.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83          sk_B @ sk_A)
% 0.65/0.83         | (v5_pre_topc @ 
% 0.65/0.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83            sk_B @ sk_A)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('demod', [status(thm)], ['103', '105'])).
% 0.65/0.83  thf('107', plain,
% 0.65/0.83      (((v5_pre_topc @ 
% 0.65/0.83         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83         sk_B @ sk_A))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('simplify', [status(thm)], ['106'])).
% 0.65/0.83  thf('108', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('109', plain,
% 0.65/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.83         (~ (l1_pre_topc @ X6)
% 0.65/0.83          | ((k1_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.65/0.83              != (k2_struct_0 @ X8))
% 0.65/0.83          | ((k2_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.65/0.83              != (k2_struct_0 @ X6))
% 0.65/0.83          | ~ (v2_funct_1 @ X7)
% 0.65/0.83          | ~ (v5_pre_topc @ X7 @ X8 @ X6)
% 0.65/0.83          | ~ (v5_pre_topc @ 
% 0.65/0.83               (k2_tops_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7) @ 
% 0.65/0.83               X6 @ X8)
% 0.65/0.83          | (v3_tops_2 @ X7 @ X8 @ X6)
% 0.65/0.83          | ~ (m1_subset_1 @ X7 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.65/0.83          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.65/0.83          | ~ (v1_funct_1 @ X7)
% 0.65/0.83          | ~ (l1_pre_topc @ X8))),
% 0.65/0.83      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.65/0.83  thf('110', plain,
% 0.65/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (v5_pre_topc @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             sk_B @ sk_A)
% 0.65/0.83        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_B))
% 0.65/0.83        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_A))
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['108', '109'])).
% 0.65/0.83  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('113', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('115', plain,
% 0.65/0.83      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (v5_pre_topc @ 
% 0.65/0.83             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.83             sk_B @ sk_A)
% 0.65/0.83        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_B))
% 0.65/0.83        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_A)))),
% 0.65/0.83      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.65/0.83  thf('116', plain,
% 0.65/0.83      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83           != (k2_struct_0 @ sk_A))
% 0.65/0.83         | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83             != (k2_struct_0 @ sk_B))
% 0.65/0.83         | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['107', '115'])).
% 0.65/0.83  thf('117', plain,
% 0.65/0.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_B)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.65/0.83      inference('split', [status(esa)], ['26'])).
% 0.65/0.83  thf('118', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('split', [status(esa)], ['28'])).
% 0.65/0.83  thf('119', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('120', plain,
% 0.65/0.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.83         (~ (v2_pre_topc @ X12)
% 0.65/0.83          | ~ (l1_pre_topc @ X12)
% 0.65/0.83          | (m1_subset_1 @ (sk_D @ X13 @ X12 @ X14) @ 
% 0.65/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.83          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.65/0.83          | ~ (m1_subset_1 @ X13 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.65/0.83          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.65/0.83          | ~ (v1_funct_1 @ X13)
% 0.65/0.83          | ~ (l1_pre_topc @ X14)
% 0.65/0.83          | ~ (v2_pre_topc @ X14))),
% 0.65/0.83      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.65/0.83  thf('121', plain,
% 0.65/0.83      ((~ (v2_pre_topc @ sk_A)
% 0.65/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.65/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B)
% 0.65/0.83        | ~ (v2_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['119', '120'])).
% 0.65/0.83  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('125', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('127', plain, ((v2_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('128', plain,
% 0.65/0.83      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.65/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('demod', [status(thm)],
% 0.65/0.83                ['121', '122', '123', '124', '125', '126', '127'])).
% 0.65/0.83  thf('129', plain,
% 0.65/0.83      ((![X24 : $i]:
% 0.65/0.83          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83               = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                  (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C @ X24)))))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('split', [status(esa)], ['30'])).
% 0.65/0.83  thf('130', plain,
% 0.65/0.83      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83             sk_C @ (k2_pre_topc @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.65/0.83             = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                 sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['128', '129'])).
% 0.65/0.83  thf('131', plain,
% 0.65/0.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.83         (~ (v2_pre_topc @ X12)
% 0.65/0.83          | ~ (l1_pre_topc @ X12)
% 0.65/0.83          | ~ (r1_tarski @ 
% 0.65/0.83               (k2_pre_topc @ X14 @ 
% 0.65/0.83                (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 0.65/0.83                 X13 @ (sk_D @ X13 @ X12 @ X14))) @ 
% 0.65/0.83               (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 0.65/0.83                X13 @ (k2_pre_topc @ X12 @ (sk_D @ X13 @ X12 @ X14))))
% 0.65/0.83          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.65/0.83          | ~ (m1_subset_1 @ X13 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.65/0.83          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.65/0.83          | ~ (v1_funct_1 @ X13)
% 0.65/0.83          | ~ (l1_pre_topc @ X14)
% 0.65/0.83          | ~ (v2_pre_topc @ X14))),
% 0.65/0.83      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.65/0.83  thf('132', plain,
% 0.65/0.83      (((~ (r1_tarski @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.65/0.83            (k2_pre_topc @ sk_A @ 
% 0.65/0.83             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.65/0.83         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         | ~ (v2_pre_topc @ sk_A)
% 0.65/0.83         | ~ (l1_pre_topc @ sk_A)
% 0.65/0.83         | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83         | ~ (m1_subset_1 @ sk_C @ 
% 0.65/0.83              (k1_zfmisc_1 @ 
% 0.65/0.83               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.65/0.83         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         | ~ (l1_pre_topc @ sk_B)
% 0.65/0.83         | ~ (v2_pre_topc @ sk_B)))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['130', '131'])).
% 0.65/0.83  thf('133', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.65/0.83      inference('simplify', [status(thm)], ['104'])).
% 0.65/0.83  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('137', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('138', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('140', plain, ((v2_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('141', plain,
% 0.65/0.83      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('demod', [status(thm)],
% 0.65/0.83                ['132', '133', '134', '135', '136', '137', '138', '139', '140'])).
% 0.65/0.83  thf('142', plain,
% 0.65/0.83      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= ((![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('simplify', [status(thm)], ['141'])).
% 0.65/0.83  thf('143', plain,
% 0.65/0.83      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83           != (k2_struct_0 @ sk_A))
% 0.65/0.83         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.65/0.83         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('demod', [status(thm)], ['116', '117', '118', '142'])).
% 0.65/0.83  thf('144', plain,
% 0.65/0.83      ((((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83             != (k2_struct_0 @ sk_A))))
% 0.65/0.83         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('simplify', [status(thm)], ['143'])).
% 0.65/0.83  thf('145', plain,
% 0.65/0.83      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.65/0.83         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.65/0.83         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.65/0.83             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['32', '144'])).
% 0.65/0.83  thf('146', plain,
% 0.65/0.83      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.65/0.83             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.83             ((v2_funct_1 @ sk_C)) & 
% 0.65/0.83             (![X24 : $i]:
% 0.65/0.83                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83                 | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83                     = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.83                         (u1_struct_0 @ sk_B) @ sk_C @ X24))))))),
% 0.65/0.83      inference('simplify', [status(thm)], ['145'])).
% 0.65/0.83  thf('147', plain,
% 0.65/0.83      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.83          (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.83          != (k2_pre_topc @ sk_A @ 
% 0.65/0.83              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ sk_D_2)))
% 0.65/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.65/0.83        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_B))
% 0.65/0.83        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            != (k2_struct_0 @ sk_A))
% 0.65/0.83        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('148', plain,
% 0.65/0.83      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('split', [status(esa)], ['147'])).
% 0.65/0.83  thf('149', plain,
% 0.65/0.83      (~
% 0.65/0.83       (![X24 : $i]:
% 0.65/0.83          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.83           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83               sk_C @ (k2_pre_topc @ sk_B @ X24))
% 0.65/0.83               = (k2_pre_topc @ sk_A @ 
% 0.65/0.83                  (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                   sk_C @ X24))))) | 
% 0.65/0.83       ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.65/0.83       ~
% 0.65/0.83       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_B))) | 
% 0.65/0.83       ~
% 0.65/0.83       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A))) | 
% 0.65/0.83       ~ ((v2_funct_1 @ sk_C))),
% 0.65/0.83      inference('sup-', [status(thm)], ['146', '148'])).
% 0.65/0.83  thf('150', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('sat_resolution*', [status(thm)],
% 0.65/0.83                ['25', '27', '29', '31', '149'])).
% 0.65/0.83  thf('151', plain,
% 0.65/0.83      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('split', [status(esa)], ['2'])).
% 0.65/0.83  thf('152', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('153', plain,
% 0.65/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.83         (~ (l1_pre_topc @ X6)
% 0.65/0.83          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.65/0.83          | ((k1_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.65/0.83              = (k2_struct_0 @ X8))
% 0.65/0.83          | ~ (m1_subset_1 @ X7 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.65/0.83          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.65/0.83          | ~ (v1_funct_1 @ X7)
% 0.65/0.83          | ~ (l1_pre_topc @ X8))),
% 0.65/0.83      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.65/0.83  thf('154', plain,
% 0.65/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83            = (k2_struct_0 @ sk_A))
% 0.65/0.83        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['152', '153'])).
% 0.65/0.83  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('157', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('158', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('159', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A))
% 0.65/0.83        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('demod', [status(thm)], ['154', '155', '156', '157', '158'])).
% 0.65/0.83  thf('160', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A)))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['151', '159'])).
% 0.65/0.83  thf('161', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          != (k2_struct_0 @ sk_A)))
% 0.65/0.83         <= (~
% 0.65/0.83             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.65/0.83      inference('split', [status(esa)], ['147'])).
% 0.65/0.83  thf('162', plain,
% 0.65/0.83      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.65/0.83         <= (~
% 0.65/0.83             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.83                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.65/0.83             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['160', '161'])).
% 0.65/0.83  thf('163', plain,
% 0.65/0.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.83          = (k2_struct_0 @ sk_A))) | 
% 0.65/0.83       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('simplify', [status(thm)], ['162'])).
% 0.65/0.83  thf('164', plain,
% 0.65/0.83      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.83         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('split', [status(esa)], ['2'])).
% 0.65/0.83  thf('165', plain,
% 0.65/0.83      ((m1_subset_1 @ sk_C @ 
% 0.65/0.83        (k1_zfmisc_1 @ 
% 0.65/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('166', plain,
% 0.65/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.83         (~ (l1_pre_topc @ X6)
% 0.65/0.83          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.65/0.83          | (v2_funct_1 @ X7)
% 0.65/0.83          | ~ (m1_subset_1 @ X7 @ 
% 0.65/0.83               (k1_zfmisc_1 @ 
% 0.65/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.65/0.83          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.65/0.83          | ~ (v1_funct_1 @ X7)
% 0.65/0.83          | ~ (l1_pre_topc @ X8))),
% 0.65/0.83      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.65/0.83  thf('167', plain,
% 0.65/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.83        | (v2_funct_1 @ sk_C)
% 0.65/0.83        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.83      inference('sup-', [status(thm)], ['165', '166'])).
% 0.65/0.83  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('170', plain,
% 0.65/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('171', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('172', plain,
% 0.65/0.83      (((v2_funct_1 @ sk_C) | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.83      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 0.65/0.83  thf('173', plain,
% 0.65/0.83      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['164', '172'])).
% 0.65/0.83  thf('174', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.65/0.83      inference('split', [status(esa)], ['147'])).
% 0.65/0.83  thf('175', plain,
% 0.65/0.84      (((v2_funct_1 @ sk_C)) | ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('sup-', [status(thm)], ['173', '174'])).
% 0.65/0.84  thf('176', plain,
% 0.65/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('split', [status(esa)], ['2'])).
% 0.65/0.84  thf('177', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_C @ 
% 0.65/0.84        (k1_zfmisc_1 @ 
% 0.65/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('178', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.84         (~ (l1_pre_topc @ X6)
% 0.65/0.84          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.65/0.84          | ((k2_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.65/0.84              = (k2_struct_0 @ X6))
% 0.65/0.84          | ~ (m1_subset_1 @ X7 @ 
% 0.65/0.84               (k1_zfmisc_1 @ 
% 0.65/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.65/0.84          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.65/0.84          | ~ (v1_funct_1 @ X7)
% 0.65/0.84          | ~ (l1_pre_topc @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.65/0.84  thf('179', plain,
% 0.65/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.84        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84            = (k2_struct_0 @ sk_B))
% 0.65/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.84        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.84      inference('sup-', [status(thm)], ['177', '178'])).
% 0.65/0.84  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('182', plain,
% 0.65/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('183', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('184', plain,
% 0.65/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_B))
% 0.65/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('demod', [status(thm)], ['179', '180', '181', '182', '183'])).
% 0.65/0.84  thf('185', plain,
% 0.65/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_B)))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['176', '184'])).
% 0.65/0.84  thf('186', plain,
% 0.65/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          != (k2_struct_0 @ sk_B)))
% 0.65/0.84         <= (~
% 0.65/0.84             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.65/0.84      inference('split', [status(esa)], ['147'])).
% 0.65/0.84  thf('187', plain,
% 0.65/0.84      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.65/0.84         <= (~
% 0.65/0.84             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.65/0.84             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['185', '186'])).
% 0.65/0.84  thf('188', plain,
% 0.65/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.65/0.84       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('simplify', [status(thm)], ['187'])).
% 0.65/0.84  thf('189', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))) | 
% 0.65/0.84       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.65/0.84       ~
% 0.65/0.84       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.65/0.84       ~ ((v2_funct_1 @ sk_C)) | 
% 0.65/0.84       ~
% 0.65/0.84       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_A)))),
% 0.65/0.84      inference('split', [status(esa)], ['0'])).
% 0.65/0.84  thf('190', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['163', '175', '188', '25', '27', '29', '31', '149', '189'])).
% 0.65/0.84  thf('191', plain,
% 0.65/0.84      ((r1_tarski @ 
% 0.65/0.84        (k2_pre_topc @ sk_A @ 
% 0.65/0.84         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          sk_D_2)) @ 
% 0.65/0.84        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84         (k2_pre_topc @ sk_B @ sk_D_2)))),
% 0.65/0.84      inference('simpl_trail', [status(thm)], ['24', '150', '190'])).
% 0.65/0.84  thf('192', plain,
% 0.65/0.84      (![X0 : $i, X2 : $i]:
% 0.65/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.65/0.84  thf('193', plain,
% 0.65/0.84      ((~ (r1_tarski @ 
% 0.65/0.84           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84            (k2_pre_topc @ sk_B @ sk_D_2)) @ 
% 0.65/0.84           (k2_pre_topc @ sk_A @ 
% 0.65/0.84            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84             sk_C @ sk_D_2)))
% 0.65/0.84        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84            (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84            = (k2_pre_topc @ sk_A @ 
% 0.65/0.84               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                sk_C @ sk_D_2))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['191', '192'])).
% 0.65/0.84  thf('194', plain,
% 0.65/0.84      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84          != (k2_pre_topc @ sk_A @ 
% 0.65/0.84              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84               sk_C @ sk_D_2))))
% 0.65/0.84         <= (~
% 0.65/0.84             (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                sk_C @ (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84                = (k2_pre_topc @ sk_A @ 
% 0.65/0.84                   (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_2)))))),
% 0.65/0.84      inference('split', [status(esa)], ['147'])).
% 0.65/0.84  thf('195', plain,
% 0.65/0.84      (~
% 0.65/0.84       (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84          = (k2_pre_topc @ sk_A @ 
% 0.65/0.84             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84              sk_C @ sk_D_2)))) | 
% 0.65/0.84       ~
% 0.65/0.84       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.65/0.84       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.65/0.84       ~
% 0.65/0.84       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_A))) | 
% 0.65/0.84       ~ ((v2_funct_1 @ sk_C))),
% 0.65/0.84      inference('split', [status(esa)], ['147'])).
% 0.65/0.84  thf('196', plain,
% 0.65/0.84      (~
% 0.65/0.84       (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84          = (k2_pre_topc @ sk_A @ 
% 0.65/0.84             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84              sk_C @ sk_D_2))))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['25', '27', '29', '31', '149', '188', '163', '175', '195'])).
% 0.65/0.84  thf('197', plain,
% 0.65/0.84      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84         (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84         != (k2_pre_topc @ sk_A @ 
% 0.65/0.84             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84              sk_C @ sk_D_2)))),
% 0.65/0.84      inference('simpl_trail', [status(thm)], ['194', '196'])).
% 0.65/0.84  thf('198', plain,
% 0.65/0.84      (~ (r1_tarski @ 
% 0.65/0.84          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84           (k2_pre_topc @ sk_B @ sk_D_2)) @ 
% 0.65/0.84          (k2_pre_topc @ sk_A @ 
% 0.65/0.84           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84            sk_D_2)))),
% 0.65/0.84      inference('simplify_reflect-', [status(thm)], ['193', '197'])).
% 0.65/0.84  thf('199', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.65/0.84         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('split', [status(esa)], ['0'])).
% 0.65/0.84  thf('200', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['163', '175', '188', '25', '27', '29', '31', '149', '189'])).
% 0.65/0.84  thf('201', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.65/0.84      inference('simpl_trail', [status(thm)], ['199', '200'])).
% 0.65/0.84  thf('202', plain,
% 0.65/0.84      ((m1_subset_1 @ 
% 0.65/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84        (k1_zfmisc_1 @ 
% 0.65/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.65/0.84      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.65/0.84  thf('203', plain,
% 0.65/0.84      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.65/0.84         ((v2_struct_0 @ X16)
% 0.65/0.84          | ~ (v2_pre_topc @ X16)
% 0.65/0.84          | ~ (l1_pre_topc @ X16)
% 0.65/0.84          | ~ (v5_pre_topc @ X17 @ X18 @ X16)
% 0.65/0.84          | (r1_tarski @ 
% 0.65/0.84             (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17 @ 
% 0.65/0.84              (k2_pre_topc @ X18 @ X19)) @ 
% 0.65/0.84             (k2_pre_topc @ X16 @ 
% 0.65/0.84              (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ X17 @ 
% 0.65/0.84               X19)))
% 0.65/0.84          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.65/0.84          | ~ (m1_subset_1 @ X17 @ 
% 0.65/0.84               (k1_zfmisc_1 @ 
% 0.65/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.65/0.84          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.65/0.84          | ~ (v1_funct_1 @ X17)
% 0.65/0.84          | ~ (l1_pre_topc @ X18)
% 0.65/0.84          | ~ (v2_pre_topc @ X18))),
% 0.65/0.84      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.65/0.84  thf('204', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (~ (v2_pre_topc @ sk_B)
% 0.65/0.84          | ~ (l1_pre_topc @ sk_B)
% 0.65/0.84          | ~ (v1_funct_1 @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.65/0.84          | ~ (v1_funct_2 @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.65/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.84          | (r1_tarski @ 
% 0.65/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84              (k2_pre_topc @ sk_B @ X0)) @ 
% 0.65/0.84             (k2_pre_topc @ sk_A @ 
% 0.65/0.84              (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84               X0)))
% 0.65/0.84          | ~ (v5_pre_topc @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84               sk_B @ sk_A)
% 0.65/0.84          | ~ (l1_pre_topc @ sk_A)
% 0.65/0.84          | ~ (v2_pre_topc @ sk_A)
% 0.65/0.84          | (v2_struct_0 @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['202', '203'])).
% 0.65/0.84  thf('205', plain, ((v2_pre_topc @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('206', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('207', plain,
% 0.65/0.84      ((v1_funct_1 @ 
% 0.65/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.65/0.84      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.65/0.84  thf('208', plain,
% 0.65/0.84      ((v1_funct_2 @ 
% 0.65/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.65/0.84  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('210', plain, ((v2_pre_topc @ sk_A)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('211', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.84          | (r1_tarski @ 
% 0.65/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84              (k2_pre_topc @ sk_B @ X0)) @ 
% 0.65/0.84             (k2_pre_topc @ sk_A @ 
% 0.65/0.84              (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84               X0)))
% 0.65/0.84          | ~ (v5_pre_topc @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84               sk_B @ sk_A)
% 0.65/0.84          | (v2_struct_0 @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['204', '205', '206', '207', '208', '209', '210'])).
% 0.65/0.84  thf('212', plain,
% 0.65/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('split', [status(esa)], ['2'])).
% 0.65/0.84  thf('213', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_C @ 
% 0.65/0.84        (k1_zfmisc_1 @ 
% 0.65/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('214', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.84         (~ (l1_pre_topc @ X6)
% 0.65/0.84          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.65/0.84          | (v5_pre_topc @ 
% 0.65/0.84             (k2_tops_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7) @ X6 @ 
% 0.65/0.84             X8)
% 0.65/0.84          | ~ (m1_subset_1 @ X7 @ 
% 0.65/0.84               (k1_zfmisc_1 @ 
% 0.65/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.65/0.84          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.65/0.84          | ~ (v1_funct_1 @ X7)
% 0.65/0.84          | ~ (l1_pre_topc @ X8))),
% 0.65/0.84      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.65/0.84  thf('215', plain,
% 0.65/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.65/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.65/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.65/0.84        | (v5_pre_topc @ 
% 0.65/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84           sk_B @ sk_A)
% 0.65/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.65/0.84        | ~ (l1_pre_topc @ sk_B))),
% 0.65/0.84      inference('sup-', [status(thm)], ['213', '214'])).
% 0.65/0.84  thf('216', plain, ((l1_pre_topc @ sk_A)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('218', plain,
% 0.65/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('219', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('220', plain,
% 0.65/0.84      (((v5_pre_topc @ 
% 0.65/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84         sk_B @ sk_A)
% 0.65/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('demod', [status(thm)], ['215', '216', '217', '218', '219'])).
% 0.65/0.84  thf('221', plain,
% 0.65/0.84      (((v5_pre_topc @ 
% 0.65/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84         sk_B @ sk_A)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['212', '220'])).
% 0.65/0.84  thf('222', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['25', '27', '29', '31', '149'])).
% 0.65/0.84  thf('223', plain,
% 0.65/0.84      ((v5_pre_topc @ 
% 0.65/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84        sk_B @ sk_A)),
% 0.65/0.84      inference('simpl_trail', [status(thm)], ['221', '222'])).
% 0.65/0.84  thf('224', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.84          | (r1_tarski @ 
% 0.65/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84              (k2_pre_topc @ sk_B @ X0)) @ 
% 0.65/0.84             (k2_pre_topc @ sk_A @ 
% 0.65/0.84              (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84               X0)))
% 0.65/0.84          | (v2_struct_0 @ sk_A))),
% 0.65/0.84      inference('demod', [status(thm)], ['211', '223'])).
% 0.65/0.84  thf('225', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('226', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((r1_tarski @ 
% 0.65/0.84           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84            (k2_pre_topc @ sk_B @ X0)) @ 
% 0.65/0.84           (k2_pre_topc @ sk_A @ 
% 0.65/0.84            (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84             X0)))
% 0.65/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('clc', [status(thm)], ['224', '225'])).
% 0.65/0.84  thf('227', plain,
% 0.65/0.84      ((r1_tarski @ 
% 0.65/0.84        (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84         (k2_pre_topc @ sk_B @ sk_D_2)) @ 
% 0.65/0.84        (k2_pre_topc @ sk_A @ 
% 0.65/0.84         (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84          sk_D_2)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['201', '226'])).
% 0.65/0.84  thf('228', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.65/0.84         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('split', [status(esa)], ['0'])).
% 0.65/0.84  thf('229', plain,
% 0.65/0.84      (![X3 : $i, X4 : $i]:
% 0.65/0.84         (~ (l1_pre_topc @ X3)
% 0.65/0.84          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.65/0.84          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.65/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.65/0.84      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.65/0.84  thf('230', plain,
% 0.65/0.84      ((((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D_2) @ 
% 0.65/0.84          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.84         | ~ (l1_pre_topc @ sk_B)))
% 0.65/0.84         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['228', '229'])).
% 0.65/0.84  thf('231', plain, ((l1_pre_topc @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('232', plain,
% 0.65/0.84      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D_2) @ 
% 0.65/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.65/0.84         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('demod', [status(thm)], ['230', '231'])).
% 0.65/0.84  thf('233', plain,
% 0.65/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84          = (k2_struct_0 @ sk_B)))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['176', '184'])).
% 0.65/0.84  thf('234', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.65/0.84            != (k2_struct_0 @ sk_B))
% 0.65/0.84          | ~ (v2_funct_1 @ sk_C)
% 0.65/0.84          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84              sk_C @ X0)
% 0.65/0.84              = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                  sk_C) @ 
% 0.65/0.84                 X0))
% 0.65/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('demod', [status(thm)], ['71', '74', '75', '76', '79'])).
% 0.65/0.84  thf('235', plain,
% 0.65/0.84      ((![X0 : $i]:
% 0.65/0.84          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.65/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.84           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84               sk_C @ X0)
% 0.65/0.84               = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                   sk_C) @ 
% 0.65/0.84                  X0))
% 0.65/0.84           | ~ (v2_funct_1 @ sk_C)))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['233', '234'])).
% 0.65/0.84  thf('236', plain,
% 0.65/0.84      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['164', '172'])).
% 0.65/0.84  thf('237', plain,
% 0.65/0.84      ((![X0 : $i]:
% 0.65/0.84          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.65/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.65/0.84           | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84               sk_C @ X0)
% 0.65/0.84               = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84                   sk_C) @ 
% 0.65/0.84                  X0))))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['235', '236'])).
% 0.65/0.84  thf('238', plain,
% 0.65/0.84      ((![X0 : $i]:
% 0.65/0.84          (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84             sk_C @ X0)
% 0.65/0.84             = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84                X0))
% 0.65/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('simplify', [status(thm)], ['237'])).
% 0.65/0.84  thf('239', plain,
% 0.65/0.84      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84          = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84             (k2_pre_topc @ sk_B @ sk_D_2))))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.65/0.84             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['232', '238'])).
% 0.65/0.84  thf('240', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['25', '27', '29', '31', '149'])).
% 0.65/0.84  thf('241', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['163', '175', '188', '25', '27', '29', '31', '149', '189'])).
% 0.65/0.84  thf('242', plain,
% 0.65/0.84      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84         (k2_pre_topc @ sk_B @ sk_D_2))
% 0.65/0.84         = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84            (k2_pre_topc @ sk_B @ sk_D_2)))),
% 0.65/0.84      inference('simpl_trail', [status(thm)], ['239', '240', '241'])).
% 0.65/0.84  thf('243', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.65/0.84         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('split', [status(esa)], ['0'])).
% 0.65/0.84  thf('244', plain,
% 0.65/0.84      ((![X0 : $i]:
% 0.65/0.84          (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.65/0.84             sk_C @ X0)
% 0.65/0.84             = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84                X0))
% 0.65/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.65/0.84      inference('simplify', [status(thm)], ['237'])).
% 0.65/0.84  thf('245', plain,
% 0.65/0.84      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          sk_D_2)
% 0.65/0.84          = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84             sk_D_2)))
% 0.65/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.65/0.84             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['243', '244'])).
% 0.65/0.84  thf('246', plain, (((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['25', '27', '29', '31', '149'])).
% 0.65/0.84  thf('247', plain,
% 0.65/0.84      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.65/0.84      inference('sat_resolution*', [status(thm)],
% 0.65/0.84                ['163', '175', '188', '25', '27', '29', '31', '149', '189'])).
% 0.65/0.84  thf('248', plain,
% 0.65/0.84      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84         sk_D_2)
% 0.65/0.84         = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.65/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.65/0.84            sk_D_2))),
% 0.65/0.84      inference('simpl_trail', [status(thm)], ['245', '246', '247'])).
% 0.65/0.84  thf('249', plain,
% 0.65/0.84      ((r1_tarski @ 
% 0.65/0.84        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84         (k2_pre_topc @ sk_B @ sk_D_2)) @ 
% 0.65/0.84        (k2_pre_topc @ sk_A @ 
% 0.65/0.84         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.65/0.84          sk_D_2)))),
% 0.65/0.84      inference('demod', [status(thm)], ['227', '242', '248'])).
% 0.65/0.84  thf('250', plain, ($false), inference('demod', [status(thm)], ['198', '249'])).
% 0.65/0.84  
% 0.65/0.84  % SZS output end Refutation
% 0.65/0.84  
% 0.65/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
