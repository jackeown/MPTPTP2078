%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VlMujLGXap

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:31 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  254 ( 834 expanded)
%              Number of leaves         :   38 ( 255 expanded)
%              Depth                    :   23
%              Number of atoms          : 4804 (35180 expanded)
%              Number of equality atoms :  148 (1319 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

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
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
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
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 )
        = ( k2_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
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
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v3_tops_2 @ X7 @ X8 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

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

thf('55',plain,(
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

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X9 @ X10 @ X11 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','64','70','71','72'])).

thf('74',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('75',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','64','70','71','72'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('77',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('78',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['42'])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ X21 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 ) @ X21 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 )
       != ( k2_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t67_tops_2])).

thf('85',plain,(
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('87',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['85','88','89','90','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ sk_C )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('98',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','97'])).

thf('99',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','64','70','71','72'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('101',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
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

thf('103',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('107',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('108',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109','110'])).

thf('112',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','112'])).

thf('114',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','114'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference(demod,[status(thm)],['115','117'])).

thf('119',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
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

thf('122',plain,
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
    inference('sup-',[status(thm)],['120','121'])).

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

thf('127',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,
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
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['119','127'])).

thf('129',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['42'])).

thf('130',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('131',plain,(
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

thf('132',plain,(
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

thf('133',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

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
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('144',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
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

thf('146',plain,
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
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('148',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','152','153','154'])).

thf('156',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','158'])).

thf('160',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','160'])).

thf('162',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('164',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X31 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X31 ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['165'])).

thf('167',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['165'])).

thf('168',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('169',plain,(
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

thf('170',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v3_tops_2 @ X25 @ X26 @ X24 )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) @ X25 ) @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_tops_2])).

thf('171',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['171','172','173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['168','178'])).

thf('180',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

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

thf('181',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X29 @ X28 @ X27 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) @ X29 @ ( k2_pre_topc @ X27 @ X30 ) )
        = ( k2_pre_topc @ X28 @ ( k8_relset_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('182',plain,(
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
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('186',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186','187','188'])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
          = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['179','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
          = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
      = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_3 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['167','192'])).

thf('194',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['165'])).

thf('195',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['85','88','89','90','93'])).

thf('197',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('199',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_3 ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['194','200'])).

thf('202',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['193','201'])).

thf('203',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['165'])).

thf('204',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('205',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['199'])).

thf('209',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_3 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['202','209'])).

thf('211',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
   <= ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('212',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
   <= ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
       != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_3 ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_3 ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','27','40','41','43','45','47','164','166','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VlMujLGXap
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 397 iterations in 0.373s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.61/0.84  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.61/0.84  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.84  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.61/0.84  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.61/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.84  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.61/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.61/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.84  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.61/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.84  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.61/0.84  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.61/0.84  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.61/0.84  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.61/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.84  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.61/0.84  thf(t74_tops_2, conjecture,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.61/0.84             ( l1_pre_topc @ B ) ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.84                 ( m1_subset_1 @
% 0.61/0.84                   C @ 
% 0.61/0.84                   ( k1_zfmisc_1 @
% 0.61/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.84               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.61/0.84                 ( ( ( k1_relset_1 @
% 0.61/0.84                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                     ( k2_struct_0 @ A ) ) & 
% 0.61/0.84                   ( ( k2_relset_1 @
% 0.61/0.84                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                     ( k2_struct_0 @ B ) ) & 
% 0.61/0.84                   ( v2_funct_1 @ C ) & 
% 0.61/0.84                   ( ![D:$i]:
% 0.61/0.84                     ( ( m1_subset_1 @
% 0.61/0.84                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.84                       ( ( k7_relset_1 @
% 0.61/0.84                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.61/0.84                           ( k2_pre_topc @ A @ D ) ) =
% 0.61/0.84                         ( k2_pre_topc @
% 0.61/0.84                           B @ 
% 0.61/0.84                           ( k7_relset_1 @
% 0.61/0.84                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i]:
% 0.61/0.84        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84          ( ![B:$i]:
% 0.61/0.84            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.61/0.84                ( l1_pre_topc @ B ) ) =>
% 0.61/0.84              ( ![C:$i]:
% 0.61/0.84                ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.84                    ( v1_funct_2 @
% 0.61/0.84                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.84                    ( m1_subset_1 @
% 0.61/0.84                      C @ 
% 0.61/0.84                      ( k1_zfmisc_1 @
% 0.61/0.84                        ( k2_zfmisc_1 @
% 0.61/0.84                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.84                  ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.61/0.84                    ( ( ( k1_relset_1 @
% 0.61/0.84                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                        ( k2_struct_0 @ A ) ) & 
% 0.61/0.84                      ( ( k2_relset_1 @
% 0.61/0.84                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                        ( k2_struct_0 @ B ) ) & 
% 0.61/0.84                      ( v2_funct_1 @ C ) & 
% 0.61/0.84                      ( ![D:$i]:
% 0.61/0.84                        ( ( m1_subset_1 @
% 0.61/0.84                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.84                          ( ( k7_relset_1 @
% 0.61/0.84                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.61/0.84                              ( k2_pre_topc @ A @ D ) ) =
% 0.61/0.84                            ( k2_pre_topc @
% 0.61/0.84                              B @ 
% 0.61/0.84                              ( k7_relset_1 @
% 0.61/0.84                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.61/0.84                                C @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t74_tops_2])).
% 0.61/0.84  thf('0', plain,
% 0.61/0.84      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.84          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.84          != (k2_pre_topc @ sk_B @ 
% 0.61/0.84              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ sk_D_3)))
% 0.61/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_B))
% 0.61/0.84        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_A))
% 0.61/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('1', plain,
% 0.61/0.84      (~
% 0.61/0.84       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.61/0.84       ~
% 0.61/0.84       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.84          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.84          = (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ sk_D_3)))) | 
% 0.61/0.84       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.61/0.84       ~
% 0.61/0.84       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A))) | 
% 0.61/0.84       ~ ((v2_funct_1 @ sk_C))),
% 0.61/0.84      inference('split', [status(esa)], ['0'])).
% 0.61/0.84  thf('2', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A))
% 0.61/0.84        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('3', plain,
% 0.61/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.61/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('split', [status(esa)], ['2'])).
% 0.61/0.84  thf('4', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(d5_tops_2, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( l1_pre_topc @ A ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( l1_pre_topc @ B ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.84                 ( m1_subset_1 @
% 0.61/0.84                   C @ 
% 0.61/0.84                   ( k1_zfmisc_1 @
% 0.61/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.84               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.61/0.84                 ( ( ( k1_relset_1 @
% 0.61/0.84                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                     ( k2_struct_0 @ A ) ) & 
% 0.61/0.84                   ( ( k2_relset_1 @
% 0.61/0.84                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                     ( k2_struct_0 @ B ) ) & 
% 0.61/0.84                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.61/0.84                   ( v5_pre_topc @
% 0.61/0.84                     ( k2_tops_2 @
% 0.61/0.84                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.61/0.84                     B @ A ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf('5', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.84         (~ (l1_pre_topc @ X6)
% 0.61/0.84          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.61/0.84          | ((k1_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.61/0.84              = (k2_struct_0 @ X8))
% 0.61/0.84          | ~ (m1_subset_1 @ X7 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.61/0.84          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.61/0.84          | ~ (v1_funct_1 @ X7)
% 0.61/0.84          | ~ (l1_pre_topc @ X8))),
% 0.61/0.84      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.61/0.84  thf('6', plain,
% 0.61/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            = (k2_struct_0 @ sk_A))
% 0.61/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.84  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('9', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('11', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A))
% 0.61/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.61/0.84  thf('12', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A)))
% 0.61/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['3', '11'])).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          != (k2_struct_0 @ sk_A)))
% 0.61/0.84         <= (~
% 0.61/0.84             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.61/0.84      inference('split', [status(esa)], ['0'])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.61/0.84         <= (~
% 0.61/0.84             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.61/0.84             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A))) | 
% 0.61/0.84       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('simplify', [status(thm)], ['14'])).
% 0.61/0.84  thf('16', plain,
% 0.61/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.61/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('split', [status(esa)], ['2'])).
% 0.61/0.84  thf('17', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('18', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.84         (~ (l1_pre_topc @ X6)
% 0.61/0.84          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.61/0.84          | (v2_funct_1 @ X7)
% 0.61/0.84          | ~ (m1_subset_1 @ X7 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.61/0.84          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.61/0.84          | ~ (v1_funct_1 @ X7)
% 0.61/0.84          | ~ (l1_pre_topc @ X8))),
% 0.61/0.84      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.61/0.84  thf('19', plain,
% 0.61/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | (v2_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.84  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      (((v2_funct_1 @ sk_C) | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.61/0.84  thf('25', plain,
% 0.61/0.84      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['16', '24'])).
% 0.61/0.84  thf('26', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('split', [status(esa)], ['0'])).
% 0.61/0.84  thf('27', plain,
% 0.61/0.84      (((v2_funct_1 @ sk_C)) | ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.61/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('split', [status(esa)], ['2'])).
% 0.61/0.84  thf('29', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.84         (~ (l1_pre_topc @ X6)
% 0.61/0.84          | ~ (v3_tops_2 @ X7 @ X8 @ X6)
% 0.61/0.84          | ((k2_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.61/0.84              = (k2_struct_0 @ X6))
% 0.61/0.84          | ~ (m1_subset_1 @ X7 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.61/0.84          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.61/0.84          | ~ (v1_funct_1 @ X7)
% 0.61/0.84          | ~ (l1_pre_topc @ X8))),
% 0.61/0.84      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.61/0.84  thf('31', plain,
% 0.61/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            = (k2_struct_0 @ sk_B))
% 0.61/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.84  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('34', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('36', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B))
% 0.61/0.84        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.61/0.84  thf('37', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B)))
% 0.61/0.84         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['28', '36'])).
% 0.61/0.84  thf('38', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          != (k2_struct_0 @ sk_B)))
% 0.61/0.84         <= (~
% 0.61/0.84             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.61/0.84      inference('split', [status(esa)], ['0'])).
% 0.61/0.84  thf('39', plain,
% 0.61/0.84      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.61/0.84         <= (~
% 0.61/0.84             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.84  thf('40', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.61/0.84       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('simplify', [status(thm)], ['39'])).
% 0.61/0.84  thf('41', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A))) | 
% 0.61/0.84       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('split', [status(esa)], ['2'])).
% 0.61/0.84  thf('42', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B))
% 0.61/0.84        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('43', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.61/0.84       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('split', [status(esa)], ['42'])).
% 0.61/0.84  thf('44', plain, (((v2_funct_1 @ sk_C) | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('45', plain,
% 0.61/0.84      (((v2_funct_1 @ sk_C)) | ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('split', [status(esa)], ['44'])).
% 0.61/0.84  thf('46', plain,
% 0.61/0.84      (![X31 : $i]:
% 0.61/0.84         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84              = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                 (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C @ X31)))
% 0.61/0.84          | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('47', plain,
% 0.61/0.84      ((![X31 : $i]:
% 0.61/0.84          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84               = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C @ X31))))) | 
% 0.61/0.84       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('split', [status(esa)], ['46'])).
% 0.61/0.84  thf('48', plain,
% 0.61/0.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A)))
% 0.61/0.84         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.61/0.84      inference('split', [status(esa)], ['2'])).
% 0.61/0.84  thf('49', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(dt_k2_tops_2, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.84       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.61/0.84         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.61/0.84         ( m1_subset_1 @
% 0.61/0.84           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.61/0.84           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.61/0.84  thf('50', plain,
% 0.61/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.84         ((m1_subset_1 @ (k2_tops_2 @ X9 @ X10 @ X11) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.61/0.84          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.61/0.84          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.61/0.84          | ~ (v1_funct_1 @ X11))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.61/0.84  thf('51', plain,
% 0.61/0.84      ((~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84           (k1_zfmisc_1 @ 
% 0.61/0.84            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['49', '50'])).
% 0.61/0.84  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('53', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('54', plain,
% 0.61/0.84      ((m1_subset_1 @ 
% 0.61/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.61/0.84  thf(t56_tops_2, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.84                 ( m1_subset_1 @
% 0.61/0.84                   C @ 
% 0.61/0.84                   ( k1_zfmisc_1 @
% 0.61/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.84               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.61/0.84                 ( ![D:$i]:
% 0.61/0.84                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.61/0.84                     ( r1_tarski @
% 0.61/0.84                       ( k2_pre_topc @
% 0.61/0.84                         A @ 
% 0.61/0.84                         ( k8_relset_1 @
% 0.61/0.84                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ 
% 0.61/0.84                       ( k8_relset_1 @
% 0.61/0.84                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.61/0.84                         ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf('55', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.84         (~ (v2_pre_topc @ X12)
% 0.61/0.84          | ~ (l1_pre_topc @ X12)
% 0.61/0.84          | (m1_subset_1 @ (sk_D @ X13 @ X12 @ X14) @ 
% 0.61/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.84          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.61/0.84          | ~ (m1_subset_1 @ X13 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.61/0.84          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.61/0.84          | ~ (v1_funct_1 @ X13)
% 0.61/0.84          | ~ (l1_pre_topc @ X14)
% 0.61/0.84          | ~ (v2_pre_topc @ X14))),
% 0.61/0.84      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.61/0.84  thf('56', plain,
% 0.61/0.84      ((~ (v2_pre_topc @ sk_B)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B)
% 0.61/0.84        | ~ (v1_funct_1 @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.61/0.84        | ~ (v1_funct_2 @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.61/0.84        | (v5_pre_topc @ 
% 0.61/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84           sk_B @ sk_A)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (sk_D @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_A @ sk_B) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | ~ (v2_pre_topc @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.61/0.84  thf('57', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('59', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('60', plain,
% 0.61/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.84         ((v1_funct_1 @ (k2_tops_2 @ X9 @ X10 @ X11))
% 0.61/0.84          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.61/0.84          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.61/0.84          | ~ (v1_funct_1 @ X11))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.61/0.84  thf('61', plain,
% 0.61/0.84      ((~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | (v1_funct_1 @ 
% 0.61/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.61/0.84  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('63', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('64', plain,
% 0.61/0.84      ((v1_funct_1 @ 
% 0.61/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.61/0.84      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.61/0.84  thf('65', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('66', plain,
% 0.61/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.84         ((v1_funct_2 @ (k2_tops_2 @ X9 @ X10 @ X11) @ X10 @ X9)
% 0.61/0.84          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.61/0.84          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.61/0.84          | ~ (v1_funct_1 @ X11))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.61/0.84  thf('67', plain,
% 0.61/0.84      ((~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | (v1_funct_2 @ 
% 0.61/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.84  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('69', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('70', plain,
% 0.61/0.84      ((v1_funct_2 @ 
% 0.61/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.61/0.84  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('73', plain,
% 0.61/0.84      (((v5_pre_topc @ 
% 0.61/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84         sk_B @ sk_A)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (sk_D @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_A @ sk_B) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['56', '57', '58', '64', '70', '71', '72'])).
% 0.61/0.84  thf('74', plain,
% 0.61/0.84      ((![X31 : $i]:
% 0.61/0.84          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84               = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C @ X31)))))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('split', [status(esa)], ['46'])).
% 0.61/0.84  thf('75', plain,
% 0.61/0.84      ((((v5_pre_topc @ 
% 0.61/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84          sk_B @ sk_A)
% 0.61/0.84         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84             sk_C @ 
% 0.61/0.84             (k2_pre_topc @ sk_A @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B)))
% 0.61/0.84             = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                 sk_C @ 
% 0.61/0.84                 (sk_D @ 
% 0.61/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C) @ 
% 0.61/0.84                  sk_A @ sk_B))))))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['73', '74'])).
% 0.61/0.84  thf('76', plain,
% 0.61/0.84      (((v5_pre_topc @ 
% 0.61/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84         sk_B @ sk_A)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (sk_D @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_A @ sk_B) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['56', '57', '58', '64', '70', '71', '72'])).
% 0.61/0.84  thf(dt_k2_pre_topc, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( l1_pre_topc @ A ) & 
% 0.61/0.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.84       ( m1_subset_1 @
% 0.61/0.84         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.61/0.84  thf('77', plain,
% 0.61/0.84      (![X3 : $i, X4 : $i]:
% 0.61/0.84         (~ (l1_pre_topc @ X3)
% 0.61/0.84          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.61/0.84          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.61/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.61/0.84  thf('78', plain,
% 0.61/0.84      (((v5_pre_topc @ 
% 0.61/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84         sk_B @ sk_A)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (k2_pre_topc @ sk_A @ 
% 0.61/0.84            (sk_D @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             sk_A @ sk_B)) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84        | ~ (l1_pre_topc @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['76', '77'])).
% 0.61/0.84  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('80', plain,
% 0.61/0.84      (((v5_pre_topc @ 
% 0.61/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84         sk_B @ sk_A)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (k2_pre_topc @ sk_A @ 
% 0.61/0.84            (sk_D @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             sk_A @ sk_B)) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)], ['78', '79'])).
% 0.61/0.84  thf('81', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('split', [status(esa)], ['44'])).
% 0.61/0.84  thf('82', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.61/0.84      inference('split', [status(esa)], ['42'])).
% 0.61/0.84  thf('83', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t67_tops_2, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( l1_struct_0 @ A ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( l1_struct_0 @ B ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.84                 ( m1_subset_1 @
% 0.61/0.84                   C @ 
% 0.61/0.84                   ( k1_zfmisc_1 @
% 0.61/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.84               ( ![D:$i]:
% 0.61/0.84                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.84                   ( ( ( ( k2_relset_1 @
% 0.61/0.84                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.84                         ( k2_struct_0 @ B ) ) & 
% 0.61/0.84                       ( v2_funct_1 @ C ) ) =>
% 0.61/0.84                     ( ( k7_relset_1 @
% 0.61/0.84                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.61/0.84                       ( k8_relset_1 @
% 0.61/0.84                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.61/0.84                         ( k2_tops_2 @
% 0.61/0.84                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.61/0.84                         D ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf('84', plain,
% 0.61/0.84      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.61/0.84         (~ (l1_struct_0 @ X20)
% 0.61/0.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.61/0.84          | ((k7_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23 @ 
% 0.61/0.84              X21)
% 0.61/0.84              = (k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22) @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23) @ 
% 0.61/0.84                 X21))
% 0.61/0.84          | ~ (v2_funct_1 @ X23)
% 0.61/0.84          | ((k2_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23)
% 0.61/0.84              != (k2_struct_0 @ X20))
% 0.61/0.84          | ~ (m1_subset_1 @ X23 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.61/0.84          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.61/0.84          | ~ (v1_funct_1 @ X23)
% 0.61/0.84          | ~ (l1_struct_0 @ X22))),
% 0.61/0.84      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.61/0.84  thf('85', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (l1_struct_0 @ sk_A)
% 0.61/0.84          | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84              != (k2_struct_0 @ sk_B))
% 0.61/0.84          | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ X0)
% 0.61/0.84              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 X0))
% 0.61/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84          | ~ (l1_struct_0 @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['83', '84'])).
% 0.61/0.84  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(dt_l1_pre_topc, axiom,
% 0.61/0.84    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.61/0.84  thf('87', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.61/0.84  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.61/0.84      inference('sup-', [status(thm)], ['86', '87'])).
% 0.61/0.84  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('90', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('92', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.61/0.84  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.61/0.84      inference('sup-', [status(thm)], ['91', '92'])).
% 0.61/0.84  thf('94', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_B))
% 0.61/0.84          | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ X0)
% 0.61/0.84              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 X0))
% 0.61/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)], ['85', '88', '89', '90', '93'])).
% 0.61/0.84  thf('95', plain,
% 0.61/0.84      ((![X0 : $i]:
% 0.61/0.84          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.61/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ X0)
% 0.61/0.84               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C) @ 
% 0.61/0.84                  X0))
% 0.61/0.84           | ~ (v2_funct_1 @ sk_C)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['82', '94'])).
% 0.61/0.84  thf('96', plain,
% 0.61/0.84      ((![X0 : $i]:
% 0.61/0.84          (~ (v2_funct_1 @ sk_C)
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ X0)
% 0.61/0.84               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C) @ 
% 0.61/0.84                  X0))
% 0.61/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['95'])).
% 0.61/0.84  thf('97', plain,
% 0.61/0.84      ((![X0 : $i]:
% 0.61/0.84          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ X0)
% 0.61/0.84               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C) @ 
% 0.61/0.84                  X0))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['81', '96'])).
% 0.61/0.84  thf('98', plain,
% 0.61/0.84      ((((v5_pre_topc @ 
% 0.61/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84          sk_B @ sk_A)
% 0.61/0.84         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84             sk_C @ 
% 0.61/0.84             (k2_pre_topc @ sk_A @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B)))
% 0.61/0.84             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84                (k2_pre_topc @ sk_A @ 
% 0.61/0.84                 (sk_D @ 
% 0.61/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C) @ 
% 0.61/0.84                  sk_A @ sk_B))))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['80', '97'])).
% 0.61/0.84  thf('99', plain,
% 0.61/0.84      (((v5_pre_topc @ 
% 0.61/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84         sk_B @ sk_A)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (sk_D @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_A @ sk_B) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['56', '57', '58', '64', '70', '71', '72'])).
% 0.61/0.84  thf('100', plain,
% 0.61/0.84      ((![X0 : $i]:
% 0.61/0.84          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ X0)
% 0.61/0.84               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C) @ 
% 0.61/0.84                  X0))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['81', '96'])).
% 0.61/0.84  thf('101', plain,
% 0.61/0.84      ((((v5_pre_topc @ 
% 0.61/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84          sk_B @ sk_A)
% 0.61/0.84         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84             sk_C @ 
% 0.61/0.84             (sk_D @ 
% 0.61/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84              sk_A @ sk_B))
% 0.61/0.84             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84                (sk_D @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 sk_A @ sk_B)))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['99', '100'])).
% 0.61/0.84  thf('102', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.84         (~ (v2_pre_topc @ X12)
% 0.61/0.84          | ~ (l1_pre_topc @ X12)
% 0.61/0.84          | ~ (r1_tarski @ 
% 0.61/0.84               (k2_pre_topc @ X14 @ 
% 0.61/0.84                (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 0.61/0.84                 X13 @ (sk_D @ X13 @ X12 @ X14))) @ 
% 0.61/0.84               (k8_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 0.61/0.84                X13 @ (k2_pre_topc @ X12 @ (sk_D @ X13 @ X12 @ X14))))
% 0.61/0.84          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.61/0.84          | ~ (m1_subset_1 @ X13 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.61/0.84          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.61/0.84          | ~ (v1_funct_1 @ X13)
% 0.61/0.84          | ~ (l1_pre_topc @ X14)
% 0.61/0.84          | ~ (v2_pre_topc @ X14))),
% 0.61/0.84      inference('cnf', [status(esa)], [t56_tops_2])).
% 0.61/0.84  thf('103', plain,
% 0.61/0.84      (((~ (r1_tarski @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))) @ 
% 0.61/0.84            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             (k2_pre_topc @ sk_A @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))))
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)
% 0.61/0.84         | ~ (v2_pre_topc @ sk_B)
% 0.61/0.84         | ~ (l1_pre_topc @ sk_B)
% 0.61/0.84         | ~ (v1_funct_1 @ 
% 0.61/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.61/0.84         | ~ (v1_funct_2 @ 
% 0.61/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.61/0.84         | ~ (m1_subset_1 @ 
% 0.61/0.84              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84              (k1_zfmisc_1 @ 
% 0.61/0.84               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)
% 0.61/0.84         | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84         | ~ (v2_pre_topc @ sk_A)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['101', '102'])).
% 0.61/0.84  thf('104', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('106', plain,
% 0.61/0.84      ((v1_funct_1 @ 
% 0.61/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.61/0.84      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.61/0.84  thf('107', plain,
% 0.61/0.84      ((v1_funct_2 @ 
% 0.61/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.61/0.84  thf('108', plain,
% 0.61/0.84      ((m1_subset_1 @ 
% 0.61/0.84        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.61/0.84      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.61/0.84  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('111', plain,
% 0.61/0.84      (((~ (r1_tarski @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))) @ 
% 0.61/0.84            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             (k2_pre_topc @ sk_A @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))))
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['103', '104', '105', '106', '107', '108', '109', '110'])).
% 0.61/0.84  thf('112', plain,
% 0.61/0.84      ((((v5_pre_topc @ 
% 0.61/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84          sk_B @ sk_A)
% 0.61/0.84         | ~ (r1_tarski @ 
% 0.61/0.84              (k2_pre_topc @ sk_B @ 
% 0.61/0.84               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C @ 
% 0.61/0.84                (sk_D @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 sk_A @ sk_B))) @ 
% 0.61/0.84              (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               (k2_pre_topc @ sk_A @ 
% 0.61/0.84                (sk_D @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 sk_A @ sk_B))))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['111'])).
% 0.61/0.84  thf('113', plain,
% 0.61/0.84      (((~ (r1_tarski @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))) @ 
% 0.61/0.84            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84             sk_C @ 
% 0.61/0.84             (k2_pre_topc @ sk_A @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))))
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['98', '112'])).
% 0.61/0.84  thf('114', plain,
% 0.61/0.84      ((((v5_pre_topc @ 
% 0.61/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84          sk_B @ sk_A)
% 0.61/0.84         | ~ (r1_tarski @ 
% 0.61/0.84              (k2_pre_topc @ sk_B @ 
% 0.61/0.84               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C @ 
% 0.61/0.84                (sk_D @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 sk_A @ sk_B))) @ 
% 0.61/0.84              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ 
% 0.61/0.84               (k2_pre_topc @ sk_A @ 
% 0.61/0.84                (sk_D @ 
% 0.61/0.84                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                  sk_C) @ 
% 0.61/0.84                 sk_A @ sk_B))))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['113'])).
% 0.61/0.84  thf('115', plain,
% 0.61/0.84      (((~ (r1_tarski @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))) @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ 
% 0.61/0.84              (sk_D @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84               sk_A @ sk_B))))
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['75', '114'])).
% 0.61/0.84  thf(d10_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.84  thf('116', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('117', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.61/0.84      inference('simplify', [status(thm)], ['116'])).
% 0.61/0.84  thf('118', plain,
% 0.61/0.84      ((((v5_pre_topc @ 
% 0.61/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84          sk_B @ sk_A)
% 0.61/0.84         | (v5_pre_topc @ 
% 0.61/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84            sk_B @ sk_A)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('demod', [status(thm)], ['115', '117'])).
% 0.61/0.84  thf('119', plain,
% 0.61/0.84      (((v5_pre_topc @ 
% 0.61/0.84         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84         sk_B @ sk_A))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['118'])).
% 0.61/0.84  thf('120', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('121', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.84         (~ (l1_pre_topc @ X6)
% 0.61/0.84          | ((k1_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.61/0.84              != (k2_struct_0 @ X8))
% 0.61/0.84          | ((k2_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7)
% 0.61/0.84              != (k2_struct_0 @ X6))
% 0.61/0.84          | ~ (v2_funct_1 @ X7)
% 0.61/0.84          | ~ (v5_pre_topc @ X7 @ X8 @ X6)
% 0.61/0.84          | ~ (v5_pre_topc @ 
% 0.61/0.84               (k2_tops_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7) @ 
% 0.61/0.84               X6 @ X8)
% 0.61/0.84          | (v3_tops_2 @ X7 @ X8 @ X6)
% 0.61/0.84          | ~ (m1_subset_1 @ X7 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.61/0.84          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.61/0.84          | ~ (v1_funct_1 @ X7)
% 0.61/0.84          | ~ (l1_pre_topc @ X8))),
% 0.61/0.84      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.61/0.84  thf('122', plain,
% 0.61/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (v5_pre_topc @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             sk_B @ sk_A)
% 0.61/0.84        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_B))
% 0.61/0.84        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_A))
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['120', '121'])).
% 0.61/0.84  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('125', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('127', plain,
% 0.61/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (v5_pre_topc @ 
% 0.61/0.84             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.84             sk_B @ sk_A)
% 0.61/0.84        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_B))
% 0.61/0.84        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_A)))),
% 0.61/0.84      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.61/0.84  thf('128', plain,
% 0.61/0.84      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84           != (k2_struct_0 @ sk_A))
% 0.61/0.84         | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84             != (k2_struct_0 @ sk_B))
% 0.61/0.84         | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['119', '127'])).
% 0.61/0.84  thf('129', plain,
% 0.61/0.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.61/0.84      inference('split', [status(esa)], ['42'])).
% 0.61/0.84  thf('130', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('split', [status(esa)], ['44'])).
% 0.61/0.84  thf('131', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t57_tops_2, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.61/0.84             ( l1_pre_topc @ B ) ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.84                 ( m1_subset_1 @
% 0.61/0.84                   C @ 
% 0.61/0.84                   ( k1_zfmisc_1 @
% 0.61/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.84               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.61/0.84                 ( ![D:$i]:
% 0.61/0.84                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.84                     ( r1_tarski @
% 0.61/0.84                       ( k7_relset_1 @
% 0.61/0.84                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.61/0.84                         ( k2_pre_topc @ A @ D ) ) @ 
% 0.61/0.84                       ( k2_pre_topc @
% 0.61/0.84                         B @ 
% 0.61/0.84                         ( k7_relset_1 @
% 0.61/0.84                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf('132', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.84         ((v2_struct_0 @ X16)
% 0.61/0.84          | ~ (v2_pre_topc @ X16)
% 0.61/0.84          | ~ (l1_pre_topc @ X16)
% 0.61/0.84          | (m1_subset_1 @ (sk_D_1 @ X17 @ X16 @ X18) @ 
% 0.61/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.61/0.84          | (v5_pre_topc @ X17 @ X18 @ X16)
% 0.61/0.84          | ~ (m1_subset_1 @ X17 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.61/0.84          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.61/0.84          | ~ (v1_funct_1 @ X17)
% 0.61/0.84          | ~ (l1_pre_topc @ X18)
% 0.61/0.84          | ~ (v2_pre_topc @ X18))),
% 0.61/0.84      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.61/0.84  thf('133', plain,
% 0.61/0.84      ((~ (v2_pre_topc @ sk_A)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B)
% 0.61/0.84        | ~ (v2_pre_topc @ sk_B)
% 0.61/0.84        | (v2_struct_0 @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['131', '132'])).
% 0.61/0.84  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('137', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('138', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('139', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('140', plain,
% 0.61/0.84      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84        | (v2_struct_0 @ sk_B))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['133', '134', '135', '136', '137', '138', '139'])).
% 0.61/0.84  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('142', plain,
% 0.61/0.84      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.61/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('clc', [status(thm)], ['140', '141'])).
% 0.61/0.84  thf('143', plain,
% 0.61/0.84      ((![X31 : $i]:
% 0.61/0.84          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84               = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C @ X31)))))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('split', [status(esa)], ['46'])).
% 0.61/0.84  thf('144', plain,
% 0.61/0.84      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84             sk_C @ (k2_pre_topc @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.61/0.84             = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                 sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))))))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['142', '143'])).
% 0.61/0.84  thf('145', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.84         ((v2_struct_0 @ X16)
% 0.61/0.84          | ~ (v2_pre_topc @ X16)
% 0.61/0.84          | ~ (l1_pre_topc @ X16)
% 0.61/0.84          | ~ (r1_tarski @ 
% 0.61/0.84               (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ 
% 0.61/0.84                X17 @ (k2_pre_topc @ X18 @ (sk_D_1 @ X17 @ X16 @ X18))) @ 
% 0.61/0.84               (k2_pre_topc @ X16 @ 
% 0.61/0.84                (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ 
% 0.61/0.84                 X17 @ (sk_D_1 @ X17 @ X16 @ X18))))
% 0.61/0.84          | (v5_pre_topc @ X17 @ X18 @ X16)
% 0.61/0.84          | ~ (m1_subset_1 @ X17 @ 
% 0.61/0.84               (k1_zfmisc_1 @ 
% 0.61/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.61/0.84          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.61/0.84          | ~ (v1_funct_1 @ X17)
% 0.61/0.84          | ~ (l1_pre_topc @ X18)
% 0.61/0.84          | ~ (v2_pre_topc @ X18))),
% 0.61/0.84      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.61/0.84  thf('146', plain,
% 0.61/0.84      (((~ (r1_tarski @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))) @ 
% 0.61/0.84            (k2_pre_topc @ sk_B @ 
% 0.61/0.84             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84              sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))))
% 0.61/0.84         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | ~ (v2_pre_topc @ sk_A)
% 0.61/0.84         | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84         | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.84         | ~ (m1_subset_1 @ sk_C @ 
% 0.61/0.84              (k1_zfmisc_1 @ 
% 0.61/0.84               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.61/0.84         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | ~ (l1_pre_topc @ sk_B)
% 0.61/0.84         | ~ (v2_pre_topc @ sk_B)
% 0.61/0.84         | (v2_struct_0 @ sk_B)))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['144', '145'])).
% 0.61/0.84  thf('147', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.61/0.84      inference('simplify', [status(thm)], ['116'])).
% 0.61/0.84  thf('148', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('151', plain,
% 0.61/0.84      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('152', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ 
% 0.61/0.84        (k1_zfmisc_1 @ 
% 0.61/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('153', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('154', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('155', plain,
% 0.61/0.84      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | (v2_struct_0 @ sk_B)))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['146', '147', '148', '149', '150', '151', '152', '153', '154'])).
% 0.61/0.84  thf('156', plain,
% 0.61/0.84      ((((v2_struct_0 @ sk_B) | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['155'])).
% 0.61/0.84  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('158', plain,
% 0.61/0.84      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.61/0.84         <= ((![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('clc', [status(thm)], ['156', '157'])).
% 0.61/0.84  thf('159', plain,
% 0.61/0.84      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84           != (k2_struct_0 @ sk_A))
% 0.61/0.84         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.61/0.84         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('demod', [status(thm)], ['128', '129', '130', '158'])).
% 0.61/0.84  thf('160', plain,
% 0.61/0.84      ((((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84         | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84             != (k2_struct_0 @ sk_A))))
% 0.61/0.84         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['159'])).
% 0.61/0.84  thf('161', plain,
% 0.61/0.84      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.61/0.84         | (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.61/0.84         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.61/0.84             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['48', '160'])).
% 0.61/0.84  thf('162', plain,
% 0.61/0.84      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.61/0.84         <= ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_A))) & 
% 0.61/0.84             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.61/0.84             ((v2_funct_1 @ sk_C)) & 
% 0.61/0.84             (![X31 : $i]:
% 0.61/0.84                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84                     = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.84                         (u1_struct_0 @ sk_B) @ sk_C @ X31))))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['161'])).
% 0.61/0.84  thf('163', plain,
% 0.61/0.84      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.61/0.84         <= (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.84      inference('split', [status(esa)], ['0'])).
% 0.61/0.84  thf('164', plain,
% 0.61/0.84      (~ ((v2_funct_1 @ sk_C)) | 
% 0.61/0.84       ~
% 0.61/0.84       (![X31 : $i]:
% 0.61/0.84          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84               sk_C @ (k2_pre_topc @ sk_A @ X31))
% 0.61/0.84               = (k2_pre_topc @ sk_B @ 
% 0.61/0.84                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.84                   sk_C @ X31))))) | 
% 0.61/0.84       ~
% 0.61/0.84       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_B))) | 
% 0.61/0.84       ~
% 0.61/0.84       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84          = (k2_struct_0 @ sk_A))) | 
% 0.61/0.84       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['162', '163'])).
% 0.61/0.84  thf('165', plain,
% 0.61/0.84      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.61/0.84        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.84            != (k2_struct_0 @ sk_B))
% 0.61/0.84        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.85            != (k2_struct_0 @ sk_A))
% 0.61/0.85        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('166', plain,
% 0.61/0.85      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.61/0.85       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.61/0.85       ~
% 0.61/0.85       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.85          = (k2_struct_0 @ sk_B))) | 
% 0.61/0.85       ~ ((v2_funct_1 @ sk_C)) | 
% 0.61/0.85       ~
% 0.61/0.85       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.85          = (k2_struct_0 @ sk_A)))),
% 0.61/0.85      inference('split', [status(esa)], ['165'])).
% 0.61/0.85  thf('167', plain,
% 0.61/0.85      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.85         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('split', [status(esa)], ['165'])).
% 0.61/0.85  thf('168', plain,
% 0.61/0.85      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('split', [status(esa)], ['2'])).
% 0.61/0.85  thf('169', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_C @ 
% 0.61/0.85        (k1_zfmisc_1 @ 
% 0.61/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(t70_tops_2, axiom,
% 0.61/0.85    (![A:$i]:
% 0.61/0.85     ( ( l1_pre_topc @ A ) =>
% 0.61/0.85       ( ![B:$i]:
% 0.61/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.61/0.85           ( ![C:$i]:
% 0.61/0.85             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.85                 ( m1_subset_1 @
% 0.61/0.85                   C @ 
% 0.61/0.85                   ( k1_zfmisc_1 @
% 0.61/0.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.85               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.61/0.85                 ( v3_tops_2 @
% 0.61/0.85                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.61/0.85                   B @ A ) ) ) ) ) ) ))).
% 0.61/0.85  thf('170', plain,
% 0.61/0.85      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.61/0.85         ((v2_struct_0 @ X24)
% 0.61/0.85          | ~ (l1_pre_topc @ X24)
% 0.61/0.85          | ~ (v3_tops_2 @ X25 @ X26 @ X24)
% 0.61/0.85          | (v3_tops_2 @ 
% 0.61/0.85             (k2_tops_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24) @ X25) @ 
% 0.61/0.85             X24 @ X26)
% 0.61/0.85          | ~ (m1_subset_1 @ X25 @ 
% 0.61/0.85               (k1_zfmisc_1 @ 
% 0.61/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))))
% 0.61/0.85          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))
% 0.61/0.85          | ~ (v1_funct_1 @ X25)
% 0.61/0.85          | ~ (l1_pre_topc @ X26))),
% 0.61/0.85      inference('cnf', [status(esa)], [t70_tops_2])).
% 0.61/0.85  thf('171', plain,
% 0.61/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.85        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.61/0.85        | (v3_tops_2 @ 
% 0.61/0.85           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85           sk_B @ sk_A)
% 0.61/0.85        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.85        | ~ (l1_pre_topc @ sk_B)
% 0.61/0.85        | (v2_struct_0 @ sk_B))),
% 0.61/0.85      inference('sup-', [status(thm)], ['169', '170'])).
% 0.61/0.85  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('174', plain,
% 0.61/0.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('175', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('176', plain,
% 0.61/0.85      (((v3_tops_2 @ 
% 0.61/0.85         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85         sk_B @ sk_A)
% 0.61/0.85        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.85        | (v2_struct_0 @ sk_B))),
% 0.61/0.85      inference('demod', [status(thm)], ['171', '172', '173', '174', '175'])).
% 0.61/0.85  thf('177', plain, (~ (v2_struct_0 @ sk_B)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('178', plain,
% 0.61/0.85      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.85        | (v3_tops_2 @ 
% 0.61/0.85           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85           sk_B @ sk_A))),
% 0.61/0.85      inference('clc', [status(thm)], ['176', '177'])).
% 0.61/0.85  thf('179', plain,
% 0.61/0.85      (((v3_tops_2 @ 
% 0.61/0.85         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85         sk_B @ sk_A)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['168', '178'])).
% 0.61/0.85  thf('180', plain,
% 0.61/0.85      ((m1_subset_1 @ 
% 0.61/0.85        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85        (k1_zfmisc_1 @ 
% 0.61/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.61/0.85      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.61/0.85  thf(t73_tops_2, axiom,
% 0.61/0.85    (![A:$i]:
% 0.61/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.85       ( ![B:$i]:
% 0.61/0.85         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.61/0.85           ( ![C:$i]:
% 0.61/0.85             ( ( ( v1_funct_1 @ C ) & 
% 0.61/0.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.61/0.85                 ( m1_subset_1 @
% 0.61/0.85                   C @ 
% 0.61/0.85                   ( k1_zfmisc_1 @
% 0.61/0.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.61/0.85               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.61/0.85                 ( ( ( k1_relset_1 @
% 0.61/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.85                     ( k2_struct_0 @ A ) ) & 
% 0.61/0.85                   ( ( k2_relset_1 @
% 0.61/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.61/0.85                     ( k2_struct_0 @ B ) ) & 
% 0.61/0.85                   ( v2_funct_1 @ C ) & 
% 0.61/0.85                   ( ![D:$i]:
% 0.61/0.85                     ( ( m1_subset_1 @
% 0.61/0.85                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.61/0.85                       ( ( k8_relset_1 @
% 0.61/0.85                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.61/0.85                           ( k2_pre_topc @ B @ D ) ) =
% 0.61/0.85                         ( k2_pre_topc @
% 0.61/0.85                           A @ 
% 0.61/0.85                           ( k8_relset_1 @
% 0.61/0.85                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.85  thf('181', plain,
% 0.61/0.85      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.61/0.85         (~ (v2_pre_topc @ X27)
% 0.61/0.85          | ~ (l1_pre_topc @ X27)
% 0.61/0.85          | ~ (v3_tops_2 @ X29 @ X28 @ X27)
% 0.61/0.85          | ((k8_relset_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27) @ X29 @ 
% 0.61/0.85              (k2_pre_topc @ X27 @ X30))
% 0.61/0.85              = (k2_pre_topc @ X28 @ 
% 0.61/0.85                 (k8_relset_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27) @ 
% 0.61/0.85                  X29 @ X30)))
% 0.61/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.61/0.85          | ~ (m1_subset_1 @ X29 @ 
% 0.61/0.85               (k1_zfmisc_1 @ 
% 0.61/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.61/0.85          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.61/0.85          | ~ (v1_funct_1 @ X29)
% 0.61/0.85          | ~ (l1_pre_topc @ X28)
% 0.61/0.85          | ~ (v2_pre_topc @ X28)
% 0.61/0.85          | (v2_struct_0 @ X28))),
% 0.61/0.85      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.61/0.85  thf('182', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((v2_struct_0 @ sk_B)
% 0.61/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.61/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.61/0.85          | ~ (v1_funct_1 @ 
% 0.61/0.85               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.61/0.85          | ~ (v1_funct_2 @ 
% 0.61/0.85               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85              (k2_pre_topc @ sk_A @ X0))
% 0.61/0.85              = (k2_pre_topc @ sk_B @ 
% 0.61/0.85                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                   sk_C) @ 
% 0.61/0.85                  X0)))
% 0.61/0.85          | ~ (v3_tops_2 @ 
% 0.61/0.85               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85               sk_B @ sk_A)
% 0.61/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.61/0.85          | ~ (v2_pre_topc @ sk_A))),
% 0.61/0.85      inference('sup-', [status(thm)], ['180', '181'])).
% 0.61/0.85  thf('183', plain, ((v2_pre_topc @ sk_B)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('184', plain, ((l1_pre_topc @ sk_B)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('185', plain,
% 0.61/0.85      ((v1_funct_1 @ 
% 0.61/0.85        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.61/0.85      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.61/0.85  thf('186', plain,
% 0.61/0.85      ((v1_funct_2 @ 
% 0.61/0.85        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.61/0.85  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('188', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('189', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((v2_struct_0 @ sk_B)
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85              (k2_pre_topc @ sk_A @ X0))
% 0.61/0.85              = (k2_pre_topc @ sk_B @ 
% 0.61/0.85                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                   sk_C) @ 
% 0.61/0.85                  X0)))
% 0.61/0.85          | ~ (v3_tops_2 @ 
% 0.61/0.85               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85               sk_B @ sk_A))),
% 0.61/0.85      inference('demod', [status(thm)],
% 0.61/0.85                ['182', '183', '184', '185', '186', '187', '188'])).
% 0.61/0.85  thf('190', plain,
% 0.61/0.85      ((![X0 : $i]:
% 0.61/0.85          (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85             (k2_pre_topc @ sk_A @ X0))
% 0.61/0.85             = (k2_pre_topc @ sk_B @ 
% 0.61/0.85                (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                  sk_C) @ 
% 0.61/0.85                 X0)))
% 0.61/0.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85           | (v2_struct_0 @ sk_B)))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['179', '189'])).
% 0.61/0.85  thf('191', plain, (~ (v2_struct_0 @ sk_B)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('192', plain,
% 0.61/0.85      ((![X0 : $i]:
% 0.61/0.85          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85           | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85               (k2_pre_topc @ sk_A @ X0))
% 0.61/0.85               = (k2_pre_topc @ sk_B @ 
% 0.61/0.85                  (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                   (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                    sk_C) @ 
% 0.61/0.85                   X0)))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('clc', [status(thm)], ['190', '191'])).
% 0.61/0.85  thf('193', plain,
% 0.61/0.85      ((((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85          = (k2_pre_topc @ sk_B @ 
% 0.61/0.85             (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85              sk_D_3))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.61/0.85             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['167', '192'])).
% 0.61/0.85  thf('194', plain,
% 0.61/0.85      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.85         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('split', [status(esa)], ['165'])).
% 0.61/0.85  thf('195', plain,
% 0.61/0.85      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.85          = (k2_struct_0 @ sk_B)))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['28', '36'])).
% 0.61/0.85  thf('196', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.61/0.85            != (k2_struct_0 @ sk_B))
% 0.61/0.85          | ~ (v2_funct_1 @ sk_C)
% 0.61/0.85          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85              sk_C @ X0)
% 0.61/0.85              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                  sk_C) @ 
% 0.61/0.85                 X0))
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.85      inference('demod', [status(thm)], ['85', '88', '89', '90', '93'])).
% 0.61/0.85  thf('197', plain,
% 0.61/0.85      ((![X0 : $i]:
% 0.61/0.85          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.61/0.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85               sk_C @ X0)
% 0.61/0.85               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                   sk_C) @ 
% 0.61/0.85                  X0))
% 0.61/0.85           | ~ (v2_funct_1 @ sk_C)))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['195', '196'])).
% 0.61/0.85  thf('198', plain,
% 0.61/0.85      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['16', '24'])).
% 0.61/0.85  thf('199', plain,
% 0.61/0.85      ((![X0 : $i]:
% 0.61/0.85          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.61/0.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85               sk_C @ X0)
% 0.61/0.85               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                   sk_C) @ 
% 0.61/0.85                  X0))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('demod', [status(thm)], ['197', '198'])).
% 0.61/0.85  thf('200', plain,
% 0.61/0.85      ((![X0 : $i]:
% 0.61/0.85          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85             sk_C @ X0)
% 0.61/0.85             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85                X0))
% 0.61/0.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('simplify', [status(thm)], ['199'])).
% 0.61/0.85  thf('201', plain,
% 0.61/0.85      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.85          sk_D_3)
% 0.61/0.85          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85             sk_D_3)))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.61/0.85             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['194', '200'])).
% 0.61/0.85  thf('202', plain,
% 0.61/0.85      ((((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85          = (k2_pre_topc @ sk_B @ 
% 0.61/0.85             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85              sk_C @ sk_D_3))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.61/0.85             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('demod', [status(thm)], ['193', '201'])).
% 0.61/0.85  thf('203', plain,
% 0.61/0.85      (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.85         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('split', [status(esa)], ['165'])).
% 0.61/0.85  thf('204', plain,
% 0.61/0.85      (![X3 : $i, X4 : $i]:
% 0.61/0.85         (~ (l1_pre_topc @ X3)
% 0.61/0.85          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.61/0.85          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.61/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.61/0.85      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.61/0.85  thf('205', plain,
% 0.61/0.85      ((((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_3) @ 
% 0.61/0.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.85         | ~ (l1_pre_topc @ sk_A)))
% 0.61/0.85         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['203', '204'])).
% 0.61/0.85  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('207', plain,
% 0.61/0.85      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_3) @ 
% 0.61/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.85         <= (((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('demod', [status(thm)], ['205', '206'])).
% 0.61/0.85  thf('208', plain,
% 0.61/0.85      ((![X0 : $i]:
% 0.61/0.85          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85             sk_C @ X0)
% 0.61/0.85             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85                X0))
% 0.61/0.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.61/0.85      inference('simplify', [status(thm)], ['199'])).
% 0.61/0.85  thf('209', plain,
% 0.61/0.85      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.85          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.61/0.85             (k2_pre_topc @ sk_A @ sk_D_3))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.61/0.85             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['207', '208'])).
% 0.61/0.85  thf('210', plain,
% 0.61/0.85      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.85          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85          = (k2_pre_topc @ sk_B @ 
% 0.61/0.85             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85              sk_C @ sk_D_3))))
% 0.61/0.85         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.61/0.85             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('sup+', [status(thm)], ['202', '209'])).
% 0.61/0.85  thf('211', plain,
% 0.61/0.85      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.85          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85          != (k2_pre_topc @ sk_B @ 
% 0.61/0.85              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85               sk_C @ sk_D_3))))
% 0.61/0.85         <= (~
% 0.61/0.85             (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                sk_C @ (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85                = (k2_pre_topc @ sk_B @ 
% 0.61/0.85                   (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_3)))))),
% 0.61/0.85      inference('split', [status(esa)], ['0'])).
% 0.61/0.85  thf('212', plain,
% 0.61/0.85      ((((k2_pre_topc @ sk_B @ 
% 0.61/0.85          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.85           sk_D_3))
% 0.61/0.85          != (k2_pre_topc @ sk_B @ 
% 0.61/0.85              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85               sk_C @ sk_D_3))))
% 0.61/0.85         <= (~
% 0.61/0.85             (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85                sk_C @ (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85                = (k2_pre_topc @ sk_B @ 
% 0.61/0.85                   (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.85                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_3)))) & 
% 0.61/0.85             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.61/0.85             ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['210', '211'])).
% 0.61/0.85  thf('213', plain,
% 0.61/0.85      (~ ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.61/0.85       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.61/0.85       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.61/0.85          (k2_pre_topc @ sk_A @ sk_D_3))
% 0.61/0.85          = (k2_pre_topc @ sk_B @ 
% 0.61/0.85             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.61/0.85              sk_C @ sk_D_3))))),
% 0.61/0.85      inference('simplify', [status(thm)], ['212'])).
% 0.61/0.85  thf('214', plain, ($false),
% 0.61/0.85      inference('sat_resolution*', [status(thm)],
% 0.61/0.85                ['1', '15', '27', '40', '41', '43', '45', '47', '164', '166', 
% 0.61/0.85                 '213'])).
% 0.61/0.85  
% 0.61/0.85  % SZS output end Refutation
% 0.61/0.85  
% 0.61/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
