%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Atl2a4ggW

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  190 (1665 expanded)
%              Number of leaves         :   26 ( 480 expanded)
%              Depth                    :   26
%              Number of atoms          : 2524 (59393 expanded)
%              Number of equality atoms :   15 ( 847 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t63_pre_topc,conjecture,(
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
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_pre_topc])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ ( sk_D @ X5 @ X4 @ X6 ) ) @ X6 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('9',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ( v4_pre_topc @ ( sk_D @ X5 @ X4 @ X6 ) @ X4 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('35',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('62',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ( v4_pre_topc @ ( sk_D @ X5 @ X4 @ X6 ) @ X4 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('76',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('81',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( v4_pre_topc @ X7 @ X4 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','91'])).

thf('93',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('94',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('95',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('100',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['92','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ ( sk_D @ X5 @ X4 @ X6 ) ) @ X6 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('106',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['106','107','108','109','110','111'])).

thf('113',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','112'])).

thf('114',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('116',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('118',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('119',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['48','52','116','119'])).

thf('121',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['42','120'])).

thf('122',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['38','121'])).

thf('123',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('124',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','127'])).

thf('129',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['42','120'])).

thf('130',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['76'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( v4_pre_topc @ X7 @ X4 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

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
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139'])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['131','140'])).

thf('142',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('143',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['48','52','116','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['141','143'])).

thf('145',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['130','144'])).

thf('146',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('147',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['38','121'])).

thf('148',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) ) )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('149',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['42','120'])).

thf('155',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['145','155'])).

thf('157',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','156'])).

thf('158',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['42','120'])).

thf('159',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['2','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['160','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Atl2a4ggW
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 69 iterations in 0.046s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(dt_u1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( u1_pre_topc @ A ) @ 
% 0.20/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.51          | ~ (l1_pre_topc @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.51  thf(dt_g1_pre_topc, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.20/0.51         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         ((l1_pre_topc @ (g1_pre_topc @ X8 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(t63_pre_topc, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.51                     ( v1_funct_2 @
% 0.20/0.51                       D @ ( u1_struct_0 @ A ) @ 
% 0.20/0.51                       ( u1_struct_0 @
% 0.20/0.51                         ( g1_pre_topc @
% 0.20/0.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.20/0.51                     ( m1_subset_1 @
% 0.20/0.51                       D @ 
% 0.20/0.51                       ( k1_zfmisc_1 @
% 0.20/0.51                         ( k2_zfmisc_1 @
% 0.20/0.51                           ( u1_struct_0 @ A ) @ 
% 0.20/0.51                           ( u1_struct_0 @
% 0.20/0.51                             ( g1_pre_topc @
% 0.20/0.51                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.20/0.51                   ( ( ( C ) = ( D ) ) =>
% 0.20/0.51                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.51                       ( v5_pre_topc @
% 0.20/0.51                         D @ A @ 
% 0.20/0.51                         ( g1_pre_topc @
% 0.20/0.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                    ( v1_funct_2 @
% 0.20/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                    ( m1_subset_1 @
% 0.20/0.51                      C @ 
% 0.20/0.51                      ( k1_zfmisc_1 @
% 0.20/0.51                        ( k2_zfmisc_1 @
% 0.20/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.51                        ( v1_funct_2 @
% 0.20/0.51                          D @ ( u1_struct_0 @ A ) @ 
% 0.20/0.51                          ( u1_struct_0 @
% 0.20/0.51                            ( g1_pre_topc @
% 0.20/0.51                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.20/0.51                        ( m1_subset_1 @
% 0.20/0.51                          D @ 
% 0.20/0.51                          ( k1_zfmisc_1 @
% 0.20/0.51                            ( k2_zfmisc_1 @
% 0.20/0.51                              ( u1_struct_0 @ A ) @ 
% 0.20/0.51                              ( u1_struct_0 @
% 0.20/0.51                                ( g1_pre_topc @
% 0.20/0.51                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.20/0.51                      ( ( ( C ) = ( D ) ) =>
% 0.20/0.51                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.51                          ( v5_pre_topc @
% 0.20/0.51                            D @ A @ 
% 0.20/0.51                            ( g1_pre_topc @
% 0.20/0.51                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t63_pre_topc])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.20/0.51          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51           (u1_struct_0 @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.20/0.51           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf(d12_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( l1_pre_topc @ B ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51                     ( ( v4_pre_topc @ D @ B ) =>
% 0.20/0.51                       ( v4_pre_topc @
% 0.20/0.51                         ( k8_relset_1 @
% 0.20/0.51                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.20/0.51                         A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (v4_pre_topc @ 
% 0.20/0.51               (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ 
% 0.20/0.51                (sk_D @ X5 @ X4 @ X6)) @ 
% 0.20/0.51               X6)
% 0.20/0.51          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((~ (v4_pre_topc @ 
% 0.20/0.51           (k10_relat_1 @ sk_C @ 
% 0.20/0.51            (sk_D @ sk_C @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51             (u1_struct_0 @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51        | ~ (m1_subset_1 @ sk_C @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51               (u1_struct_0 @ 
% 0.20/0.51                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51        (u1_struct_0 @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51        (u1_struct_0 @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((~ (v4_pre_topc @ 
% 0.20/0.51           (k10_relat_1 @ sk_C @ 
% 0.20/0.51            (sk_D @ sk_C @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10', '11', '14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | (v4_pre_topc @ (sk_D @ X5 @ X4 @ X6) @ X4)
% 0.20/0.51          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51             (u1_struct_0 @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v4_pre_topc @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51        (u1_struct_0 @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v4_pre_topc @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '24'])).
% 0.20/0.51  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((v4_pre_topc @ 
% 0.20/0.51         (sk_D @ sk_C @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X5 @ X4 @ X6) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51             (u1_struct_0 @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (m1_subset_1 @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (u1_struct_0 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51        (u1_struct_0 @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (m1_subset_1 @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (u1_struct_0 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (u1_struct_0 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '35'])).
% 0.20/0.51  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((m1_subset_1 @ 
% 0.20/0.51         (sk_D @ sk_C @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51         (k1_zfmisc_1 @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('split', [status(esa)], ['39'])).
% 0.20/0.51  thf('41', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('44', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('split', [status(esa)], ['45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.51       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('50', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.51       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('split', [status(esa)], ['51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X5 @ X4 @ X6) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.20/0.51  thf(t61_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.20/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.20/0.51           ( ( v4_pre_topc @
% 0.20/0.51               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.51             ( m1_subset_1 @
% 0.20/0.51               B @ 
% 0.20/0.51               ( k1_zfmisc_1 @
% 0.20/0.51                 ( u1_struct_0 @
% 0.20/0.51                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v4_pre_topc @ X13 @ X12)
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.51          | (m1_subset_1 @ X13 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (u1_struct_0 @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))))
% 0.20/0.51          | ~ (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (v2_pre_topc @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (u1_struct_0 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ 
% 0.20/0.51            (u1_struct_0 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | (v4_pre_topc @ (sk_D @ X5 @ X4 @ X6) @ X4)
% 0.20/0.51          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.51  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51         (k1_zfmisc_1 @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['65', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('split', [status(esa)], ['76'])).
% 0.20/0.51  thf('78', plain, (((sk_C) = (sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (v4_pre_topc @ X7 @ X4)
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ X7) @ 
% 0.20/0.51             X6)
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51               (u1_struct_0 @ 
% 0.20/0.51                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (u1_struct_0 @ 
% 0.20/0.51                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51              (u1_struct_0 @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.20/0.51              sk_C @ X0) @ 
% 0.20/0.51             sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51          | ~ (l1_pre_topc @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.51  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51        (u1_struct_0 @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51           (u1_struct_0 @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.20/0.51           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (u1_struct_0 @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51          | ~ (l1_pre_topc @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (l1_pre_topc @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51           | ~ (v4_pre_topc @ X0 @ 
% 0.20/0.51                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51           | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.51                (k1_zfmisc_1 @ 
% 0.20/0.51                 (u1_struct_0 @ 
% 0.20/0.51                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['79', '87'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (l1_pre_topc @ sk_B)
% 0.20/0.51           | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.51                (k1_zfmisc_1 @ 
% 0.20/0.51                 (u1_struct_0 @ 
% 0.20/0.51                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51           | ~ (v4_pre_topc @ X0 @ 
% 0.20/0.51                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['75', '88'])).
% 0.20/0.51  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X0 @ 
% 0.20/0.51              (k1_zfmisc_1 @ 
% 0.20/0.51               (u1_struct_0 @ 
% 0.20/0.51                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51           | ~ (v4_pre_topc @ X0 @ 
% 0.20/0.51                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51         | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51         | (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.51            sk_A)))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['74', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v4_pre_topc @ X13 @ X12)
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.51          | (v4_pre_topc @ X13 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.20/0.51          | ~ (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (v2_pre_topc @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      (((v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['98', '99'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      ((((v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.51          sk_A)
% 0.20/0.51         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('clc', [status(thm)], ['92', '100'])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.20/0.51          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (v4_pre_topc @ 
% 0.20/0.51               (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ 
% 0.20/0.51                (sk_D @ X5 @ X4 @ X6)) @ 
% 0.20/0.51               X6)
% 0.20/0.51          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      ((~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ~ (m1_subset_1 @ sk_C @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.51  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      ((~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.51           sk_A)
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['106', '107', '108', '109', '110', '111'])).
% 0.20/0.51  thf('113', plain,
% 0.20/0.51      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['101', '112'])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['113'])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.51         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['39'])).
% 0.20/0.51  thf('116', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.51       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.51  thf('117', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.51  thf('118', plain,
% 0.20/0.51      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('split', [status(esa)], ['51'])).
% 0.20/0.51  thf('119', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.51       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['117', '118'])).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['48', '52', '116', '119'])).
% 0.20/0.51  thf('121', plain,
% 0.20/0.51      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['42', '120'])).
% 0.20/0.51  thf('122', plain,
% 0.20/0.51      ((m1_subset_1 @ 
% 0.20/0.51        (sk_D @ sk_C @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (u1_struct_0 @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '121'])).
% 0.20/0.51  thf('123', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (v4_pre_topc @ X11 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (u1_struct_0 @ 
% 0.20/0.51                 (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))))
% 0.20/0.51          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.51          | ~ (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (v2_pre_topc @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.20/0.51  thf('124', plain,
% 0.20/0.51      ((~ (v2_pre_topc @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51        | ~ (v4_pre_topc @ 
% 0.20/0.51             (sk_D @ sk_C @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.20/0.51              sk_A) @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.51  thf('125', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('127', plain,
% 0.20/0.51      (((m1_subset_1 @ 
% 0.20/0.51         (sk_D @ sk_C @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51        | ~ (v4_pre_topc @ 
% 0.20/0.51             (sk_D @ sk_C @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.20/0.51              sk_A) @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.20/0.51  thf('128', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (m1_subset_1 @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '127'])).
% 0.20/0.51  thf('129', plain,
% 0.20/0.51      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['42', '120'])).
% 0.20/0.51  thf('130', plain,
% 0.20/0.51      ((m1_subset_1 @ 
% 0.20/0.51        (sk_D @ sk_C @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['128', '129'])).
% 0.20/0.51  thf('131', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.51         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['76'])).
% 0.20/0.51  thf('132', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('133', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (v5_pre_topc @ X5 @ X6 @ X4)
% 0.20/0.51          | ~ (v4_pre_topc @ X7 @ X4)
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ X7) @ 
% 0.20/0.51             X6)
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X5)
% 0.20/0.51          | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.20/0.51  thf('134', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51              sk_C @ X0) @ 
% 0.20/0.51             sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['132', '133'])).
% 0.20/0.51  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('137', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('138', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.51  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('140', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['134', '135', '136', '137', '138', '139'])).
% 0.20/0.51  thf('141', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.20/0.51           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.20/0.51         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['131', '140'])).
% 0.20/0.51  thf('142', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.20/0.51       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['45'])).
% 0.20/0.51  thf('143', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['48', '52', '116', '142'])).
% 0.20/0.51  thf('144', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v4_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['141', '143'])).
% 0.20/0.51  thf('145', plain,
% 0.20/0.51      (((v4_pre_topc @ 
% 0.20/0.51         (k10_relat_1 @ sk_C @ 
% 0.20/0.51          (sk_D @ sk_C @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.20/0.51         sk_A)
% 0.20/0.51        | ~ (v4_pre_topc @ 
% 0.20/0.51             (sk_D @ sk_C @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.20/0.51              sk_A) @ 
% 0.20/0.51             sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['130', '144'])).
% 0.20/0.51  thf('146', plain,
% 0.20/0.51      (((v4_pre_topc @ 
% 0.20/0.51         (sk_D @ sk_C @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('147', plain,
% 0.20/0.51      ((m1_subset_1 @ 
% 0.20/0.51        (sk_D @ sk_C @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (u1_struct_0 @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '121'])).
% 0.20/0.51  thf('148', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (v4_pre_topc @ X11 @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (u1_struct_0 @ 
% 0.20/0.51                 (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))))
% 0.20/0.51          | (v4_pre_topc @ X11 @ X12)
% 0.20/0.51          | ~ (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (v2_pre_topc @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.20/0.51  thf('149', plain,
% 0.20/0.51      ((~ (v2_pre_topc @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (v4_pre_topc @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           sk_B)
% 0.20/0.51        | ~ (v4_pre_topc @ 
% 0.20/0.51             (sk_D @ sk_C @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.20/0.51              sk_A) @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['147', '148'])).
% 0.20/0.51  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('152', plain,
% 0.20/0.51      (((v4_pre_topc @ 
% 0.20/0.51         (sk_D @ sk_C @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51         sk_B)
% 0.20/0.51        | ~ (v4_pre_topc @ 
% 0.20/0.51             (sk_D @ sk_C @ 
% 0.20/0.51              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.20/0.51              sk_A) @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.20/0.51  thf('153', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | (v4_pre_topc @ 
% 0.20/0.51           (sk_D @ sk_C @ 
% 0.20/0.51            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51           sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['146', '152'])).
% 0.20/0.51  thf('154', plain,
% 0.20/0.51      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['42', '120'])).
% 0.20/0.51  thf('155', plain,
% 0.20/0.51      ((v4_pre_topc @ 
% 0.20/0.51        (sk_D @ sk_C @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.20/0.51        sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['153', '154'])).
% 0.20/0.51  thf('156', plain,
% 0.20/0.51      ((v4_pre_topc @ 
% 0.20/0.51        (k10_relat_1 @ sk_C @ 
% 0.20/0.51         (sk_D @ sk_C @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.20/0.51        sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['145', '155'])).
% 0.20/0.51  thf('157', plain,
% 0.20/0.51      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.51        | ~ (l1_pre_topc @ 
% 0.20/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '156'])).
% 0.20/0.51  thf('158', plain,
% 0.20/0.51      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['42', '120'])).
% 0.20/0.51  thf('159', plain,
% 0.20/0.51      (~ (l1_pre_topc @ 
% 0.20/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['157', '158'])).
% 0.20/0.51  thf('160', plain, (~ (l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '159'])).
% 0.20/0.51  thf('161', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('162', plain, ($false), inference('demod', [status(thm)], ['160', '161'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
