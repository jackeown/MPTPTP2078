%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SZ05sMfogX

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  190 (1038 expanded)
%              Number of leaves         :   29 ( 304 expanded)
%              Depth                    :   26
%              Number of atoms          : 2344 (35400 expanded)
%              Number of equality atoms :   17 ( 536 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t62_pre_topc,conjecture,(
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
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) )).

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
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_pre_topc])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 )
        = ( k10_relat_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 @ ( sk_D @ X12 @ X11 @ X13 ) ) @ X13 )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('9',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( v4_pre_topc @ ( sk_D @ X12 @ X11 @ X13 ) @ X11 )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X11 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('45',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X11 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('59',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( v4_pre_topc @ X14 @ X11 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 @ X14 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( v4_pre_topc @ ( sk_D @ X12 @ X11 @ X13 ) @ X11 )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['75','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X7 @ X8 @ X9 @ X10 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) ) ) )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 )
        = ( k10_relat_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 @ ( sk_D @ X12 @ X11 @ X13 ) ) @ X13 )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('103',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108'])).

thf('110',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['98','109'])).

thf('111',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('112',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('114',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('115',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['45','49','112','115'])).

thf('117',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','116'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['35','117'])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['59'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( v4_pre_topc @ X14 @ X11 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 @ X14 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('134',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['45','49','112','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('136',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['121','135'])).

thf('137',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','136'])).

thf('138',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','116'])).

thf('139',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X7 @ X8 @ X9 @ X10 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('145',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X20 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','152'])).

thf('154',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','153'])).

thf('155',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','116'])).

thf('156',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['157','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SZ05sMfogX
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 89 iterations in 0.062s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(dt_u1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( u1_pre_topc @ A ) @ 
% 0.21/0.54         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X17 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (u1_pre_topc @ X17) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.21/0.54          | ~ (l1_pre_topc @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.54  thf(dt_g1_pre_topc, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.21/0.54         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((l1_pre_topc @ (g1_pre_topc @ X15 @ X16))
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(t62_pre_topc, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.54                     ( v1_funct_2 @
% 0.21/0.54                       D @ 
% 0.21/0.54                       ( u1_struct_0 @
% 0.21/0.54                         ( g1_pre_topc @
% 0.21/0.54                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.21/0.54                       ( u1_struct_0 @ B ) ) & 
% 0.21/0.54                     ( m1_subset_1 @
% 0.21/0.54                       D @ 
% 0.21/0.54                       ( k1_zfmisc_1 @
% 0.21/0.54                         ( k2_zfmisc_1 @
% 0.21/0.54                           ( u1_struct_0 @
% 0.21/0.54                             ( g1_pre_topc @
% 0.21/0.54                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.21/0.54                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.54                   ( ( ( C ) = ( D ) ) =>
% 0.21/0.54                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.54                       ( v5_pre_topc @
% 0.21/0.54                         D @ 
% 0.21/0.54                         ( g1_pre_topc @
% 0.21/0.54                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.21/0.54                         B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                    ( v1_funct_2 @
% 0.21/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.54                    ( m1_subset_1 @
% 0.21/0.54                      C @ 
% 0.21/0.54                      ( k1_zfmisc_1 @
% 0.21/0.54                        ( k2_zfmisc_1 @
% 0.21/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.54                  ( ![D:$i]:
% 0.21/0.54                    ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.54                        ( v1_funct_2 @
% 0.21/0.54                          D @ 
% 0.21/0.54                          ( u1_struct_0 @
% 0.21/0.54                            ( g1_pre_topc @
% 0.21/0.54                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.21/0.54                          ( u1_struct_0 @ B ) ) & 
% 0.21/0.54                        ( m1_subset_1 @
% 0.21/0.54                          D @ 
% 0.21/0.54                          ( k1_zfmisc_1 @
% 0.21/0.54                            ( k2_zfmisc_1 @
% 0.21/0.54                              ( u1_struct_0 @
% 0.21/0.54                                ( g1_pre_topc @
% 0.21/0.54                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.21/0.54                              ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.54                      ( ( ( C ) = ( D ) ) =>
% 0.21/0.54                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.54                          ( v5_pre_topc @
% 0.21/0.54                            D @ 
% 0.21/0.54                            ( g1_pre_topc @
% 0.21/0.54                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.21/0.54                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t62_pre_topc])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.54          | ((k8_relset_1 @ X4 @ X5 @ X3 @ X6) = (k10_relat_1 @ X3 @ X6)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ 
% 0.21/0.54           (u1_struct_0 @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           (u1_struct_0 @ sk_B) @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf(d12_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_pre_topc @ B ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.54               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                     ( ( v4_pre_topc @ D @ B ) =>
% 0.21/0.54                       ( v4_pre_topc @
% 0.21/0.54                         ( k8_relset_1 @
% 0.21/0.54                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.21/0.54                         A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v4_pre_topc @ 
% 0.21/0.54               (k8_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.21/0.54                X12 @ (sk_D @ X12 @ X11 @ X13)) @ 
% 0.21/0.54               X13)
% 0.21/0.54          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((~ (v4_pre_topc @ 
% 0.21/0.54           (k10_relat_1 @ sk_C @ 
% 0.21/0.54            (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ 
% 0.21/0.54             (u1_struct_0 @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54             (u1_struct_0 @ sk_B))
% 0.21/0.54        | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k2_zfmisc_1 @ 
% 0.21/0.54               (u1_struct_0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54               (u1_struct_0 @ sk_B))))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_D_1 @ 
% 0.21/0.54        (u1_struct_0 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54        (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ 
% 0.21/0.54        (u1_struct_0 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54        (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((~ (v4_pre_topc @ 
% 0.21/0.54           (k10_relat_1 @ sk_C @ 
% 0.21/0.54            (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10', '13', '14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | (v4_pre_topc @ (sk_D @ X12 @ X11 @ X13) @ X11)
% 0.21/0.54          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ 
% 0.21/0.54             (u1_struct_0 @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54             (u1_struct_0 @ sk_B))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (v4_pre_topc @ 
% 0.21/0.54           (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           sk_B)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ 
% 0.21/0.54        (u1_struct_0 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54        (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (v4_pre_topc @ 
% 0.21/0.54           (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v4_pre_topc @ 
% 0.21/0.54           (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           sk_B)
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '24'])).
% 0.21/0.54  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((v4_pre_topc @ 
% 0.21/0.54         (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54         sk_B)
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X12 @ X11 @ X13) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ 
% 0.21/0.54             (u1_struct_0 @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54             (u1_struct_0 @ sk_B))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ 
% 0.21/0.54        (u1_struct_0 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54        (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['36'])).
% 0.21/0.54  thf('38', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (((v5_pre_topc @ sk_C @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.21/0.54       ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('47', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.21/0.54       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X12 @ X11 @ X13) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X0)
% 0.21/0.54          | (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['59'])).
% 0.21/0.54  thf('61', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (v4_pre_topc @ X14 @ X11)
% 0.21/0.54          | (v4_pre_topc @ 
% 0.21/0.54             (k8_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12 @ 
% 0.21/0.54              X14) @ 
% 0.21/0.54             X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C @ 
% 0.21/0.54               (u1_struct_0 @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54               (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (v4_pre_topc @ 
% 0.21/0.54             (k8_relset_1 @ 
% 0.21/0.54              (u1_struct_0 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ 
% 0.21/0.54        (u1_struct_0 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54        (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ 
% 0.21/0.54           (u1_struct_0 @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           (u1_struct_0 @ sk_B) @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54           | ~ (l1_pre_topc @ 
% 0.21/0.54                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ sk_A)
% 0.21/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54           | ~ (v4_pre_topc @ X0 @ sk_B)))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '71'])).
% 0.21/0.54  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54           | ~ (v4_pre_topc @ X0 @ sk_B)))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54         | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54         | (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['57', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | (v4_pre_topc @ (sk_D @ X12 @ X11 @ X13) @ X11)
% 0.21/0.54          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      ((((v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['75', '83'])).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54          (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf(t47_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         ((r1_tarski @ (k8_relset_1 @ X7 @ X8 @ X9 @ X10) @ X7)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.21/0.54          | ~ (v1_funct_1 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | (r1_tarski @ 
% 0.21/0.54             (k8_relset_1 @ 
% 0.21/0.54              (u1_struct_0 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.21/0.54             (u1_struct_0 @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.54  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ 
% 0.21/0.54           (u1_struct_0 @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           (u1_struct_0 @ sk_B) @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54          (u1_struct_0 @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54          (k1_zfmisc_1 @ 
% 0.21/0.54           (u1_struct_0 @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.54  thf(t61_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.21/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.21/0.54           ( ( v4_pre_topc @
% 0.21/0.54               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.21/0.54             ( m1_subset_1 @
% 0.21/0.54               B @ 
% 0.21/0.54               ( k1_zfmisc_1 @
% 0.21/0.54                 ( u1_struct_0 @
% 0.21/0.54                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (v4_pre_topc @ X18 @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (u1_struct_0 @ 
% 0.21/0.54                 (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))))
% 0.21/0.54          | (v4_pre_topc @ X18 @ X19)
% 0.21/0.54          | ~ (l1_pre_topc @ X19)
% 0.21/0.54          | ~ (v2_pre_topc @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.21/0.54          | ~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.54  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.21/0.54          | ~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54         | (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.54            sk_A)))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['84', '97'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.54          | ((k8_relset_1 @ X4 @ X5 @ X3 @ X6) = (k10_relat_1 @ X3 @ X6)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.54  thf('101', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.54           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v4_pre_topc @ 
% 0.21/0.54               (k8_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.21/0.54                X12 @ (sk_D @ X12 @ X11 @ X13)) @ 
% 0.21/0.54               X13)
% 0.21/0.54          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('103', plain,
% 0.21/0.54      ((~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.54           sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.54        | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.54  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('106', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('107', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('109', plain,
% 0.21/0.54      ((~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.54           sk_A)
% 0.21/0.54        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['103', '104', '105', '106', '107', '108'])).
% 0.21/0.54  thf('110', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['98', '109'])).
% 0.21/0.54  thf('111', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['36'])).
% 0.21/0.54  thf('112', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.21/0.54       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.54  thf('113', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('114', plain,
% 0.21/0.54      ((~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v5_pre_topc @ sk_C @ 
% 0.21/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.54               sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('115', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.21/0.54       ((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.54  thf('116', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v5_pre_topc @ sk_D_1 @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['45', '49', '112', '115'])).
% 0.21/0.54  thf('117', plain,
% 0.21/0.54      (~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['39', '116'])).
% 0.21/0.54  thf('118', plain,
% 0.21/0.54      (((m1_subset_1 @ 
% 0.21/0.54         (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54        | ~ (l1_pre_topc @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['35', '117'])).
% 0.21/0.54  thf('119', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '118'])).
% 0.21/0.54  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('121', plain,
% 0.21/0.54      ((m1_subset_1 @ 
% 0.21/0.54        (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.54  thf('122', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['59'])).
% 0.21/0.54  thf('123', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('124', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v5_pre_topc @ X12 @ X13 @ X11)
% 0.21/0.54          | ~ (v4_pre_topc @ X14 @ X11)
% 0.21/0.54          | (v4_pre_topc @ 
% 0.21/0.54             (k8_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12 @ 
% 0.21/0.54              X14) @ 
% 0.21/0.54             X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.21/0.54          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.54          | ~ (v1_funct_1 @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.21/0.54  thf('125', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (v4_pre_topc @ 
% 0.21/0.54             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54              sk_C @ X0) @ 
% 0.21/0.54             sk_A)
% 0.21/0.54          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['123', '124'])).
% 0.21/0.54  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('128', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('129', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.54           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.54  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('131', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.21/0.54          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['125', '126', '127', '128', '129', '130'])).
% 0.21/0.54  thf('132', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54           | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.21/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.21/0.54         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['122', '131'])).
% 0.21/0.54  thf('133', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.21/0.54       ((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['42'])).
% 0.21/0.54  thf('134', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['45', '49', '112', '133'])).
% 0.21/0.54  thf('135', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 0.21/0.54  thf('136', plain,
% 0.21/0.54      (((v4_pre_topc @ 
% 0.21/0.54         (k10_relat_1 @ sk_C @ 
% 0.21/0.54          (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.21/0.54         sk_A)
% 0.21/0.54        | ~ (v4_pre_topc @ 
% 0.21/0.54             (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.21/0.54             sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['121', '135'])).
% 0.21/0.54  thf('137', plain,
% 0.21/0.54      (((v5_pre_topc @ sk_C @ 
% 0.21/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.21/0.54        | (v4_pre_topc @ 
% 0.21/0.54           (k10_relat_1 @ sk_C @ 
% 0.21/0.54            (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.21/0.54           sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '136'])).
% 0.21/0.54  thf('138', plain,
% 0.21/0.54      (~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['39', '116'])).
% 0.21/0.54  thf('139', plain,
% 0.21/0.54      ((v4_pre_topc @ 
% 0.21/0.54        (k10_relat_1 @ sk_C @ 
% 0.21/0.54         (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.21/0.54        sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['137', '138'])).
% 0.21/0.54  thf('140', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('141', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         ((r1_tarski @ (k8_relset_1 @ X7 @ X8 @ X9 @ X10) @ X7)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.21/0.54          | ~ (v1_funct_1 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.21/0.54  thf('142', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | (r1_tarski @ 
% 0.21/0.54             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54              sk_C @ X0) @ 
% 0.21/0.54             (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['140', '141'])).
% 0.21/0.54  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('144', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.54           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.54  thf('145', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.21/0.54  thf('146', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('147', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['145', '146'])).
% 0.21/0.54  thf('148', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (v4_pre_topc @ X20 @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.54          | (v4_pre_topc @ X20 @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.21/0.54          | ~ (l1_pre_topc @ X19)
% 0.21/0.54          | ~ (v2_pre_topc @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.21/0.54  thf('149', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.54  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('152', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54          | ~ (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.21/0.54  thf('153', plain,
% 0.21/0.54      ((v4_pre_topc @ 
% 0.21/0.54        (k10_relat_1 @ sk_C @ 
% 0.21/0.54         (sk_D @ sk_C @ sk_B @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.21/0.54        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['139', '152'])).
% 0.21/0.54  thf('154', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.54        | (v5_pre_topc @ sk_C @ 
% 0.21/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '153'])).
% 0.21/0.54  thf('155', plain,
% 0.21/0.54      (~ (v5_pre_topc @ sk_C @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['39', '116'])).
% 0.21/0.54  thf('156', plain,
% 0.21/0.54      (~ (l1_pre_topc @ 
% 0.21/0.54          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['154', '155'])).
% 0.21/0.54  thf('157', plain, (~ (l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '156'])).
% 0.21/0.54  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('159', plain, ($false), inference('demod', [status(thm)], ['157', '158'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
