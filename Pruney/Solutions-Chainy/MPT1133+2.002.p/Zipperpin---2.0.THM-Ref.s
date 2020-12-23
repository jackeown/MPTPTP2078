%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I9WLz2kWbf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:27 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  331 (2846 expanded)
%              Number of leaves         :   27 ( 836 expanded)
%              Depth                    :   43
%              Number of atoms          : 5752 (92580 expanded)
%              Number of equality atoms :   33 (1470 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ~ ( v1_pre_topc @ X4 )
      | ( X4
        = ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( g1_pre_topc @ X14 @ X15 )
       != ( g1_pre_topc @ X12 @ X13 ) )
      | ( X14 = X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t64_pre_topc,conjecture,(
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
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

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
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_pre_topc])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('40',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('56',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('72',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('77',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','91'])).

thf('93',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('94',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('111',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116'])).

thf('118',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('120',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('122',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('123',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['40','44','120','123'])).

thf('125',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['30','125'])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['15','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('134',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('141',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('142',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['139','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['138','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['151','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('161',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','124'])).

thf('163',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('171',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('172',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('176',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('180',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('181',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','183'])).

thf('185',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['169','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['168','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['72'])).

thf('192',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198'])).

thf('200',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['191','199'])).

thf('201',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['190','200'])).

thf('202',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('204',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('205',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('206',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('210',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['203','210'])).

thf('212',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('215',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['202','218'])).

thf('220',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['201','220'])).

thf('222',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['221','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('233',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['232','233'])).

thf('235',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['231','241'])).

thf('243',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['230','244'])).

thf('246',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('247',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('252',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['247','248','249','250','251'])).

thf('253',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['167','253'])).

thf('255',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('258',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['256','263'])).

thf('265',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['166','264'])).

thf('266',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['165','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('272',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['40','44','120','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['270','272'])).

thf('274',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['164','273'])).

thf('275',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('276',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('278',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('279',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['281','282','283'])).

thf('285',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['276','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('287',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('288',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['285','288'])).

thf('290',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('291',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['289','290','291','292','293'])).

thf('295',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','124'])).

thf('296',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('297',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','296'])).

thf('298',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['2','299'])).

thf('301',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    $false ),
    inference(demod,[status(thm)],['300','301'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I9WLz2kWbf
% 0.14/0.37  % Computer   : n011.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:18:57 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 666 iterations in 0.510s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.98  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.75/0.98  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.98  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.75/0.98  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.75/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.98  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.75/0.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.98  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.75/0.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.98  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.75/0.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(dt_u1_pre_topc, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( l1_pre_topc @ A ) =>
% 0.75/0.98       ( m1_subset_1 @
% 0.75/0.98         ( u1_pre_topc @ A ) @ 
% 0.75/0.98         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      (![X11 : $i]:
% 0.75/0.98         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.75/0.98           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.75/0.98          | ~ (l1_pre_topc @ X11))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.75/0.98  thf(dt_g1_pre_topc, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.75/0.98         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      (![X9 : $i, X10 : $i]:
% 0.75/0.98         ((l1_pre_topc @ (g1_pre_topc @ X9 @ X10))
% 0.75/0.98          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (![X11 : $i]:
% 0.75/0.98         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.75/0.98           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.75/0.98          | ~ (l1_pre_topc @ X11))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X9 : $i, X10 : $i]:
% 0.75/0.98         ((v1_pre_topc @ (g1_pre_topc @ X9 @ X10))
% 0.75/0.98          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (v1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.98  thf(abstractness_v1_pre_topc, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( l1_pre_topc @ A ) =>
% 0.75/0.98       ( ( v1_pre_topc @ A ) =>
% 0.75/0.98         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      (![X4 : $i]:
% 0.75/0.98         (~ (v1_pre_topc @ X4)
% 0.75/0.98          | ((X4) = (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.75/0.98          | ~ (l1_pre_topc @ X4))),
% 0.75/0.98      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X11 : $i]:
% 0.75/0.98         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.75/0.98           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.75/0.98          | ~ (l1_pre_topc @ X11))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.75/0.98  thf(free_g1_pre_topc, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98       ( ![C:$i,D:$i]:
% 0.75/0.98         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.75/0.98           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.98         (((g1_pre_topc @ X14 @ X15) != (g1_pre_topc @ X12 @ X13))
% 0.75/0.98          | ((X14) = (X12))
% 0.75/0.98          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.75/0.98      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | ((u1_struct_0 @ X0) = (X1))
% 0.75/0.98          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.75/0.98              != (g1_pre_topc @ X1 @ X2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.75/0.98          | ~ (l1_pre_topc @ X0)
% 0.75/0.98          | ~ (v1_pre_topc @ X0)
% 0.75/0.98          | ((u1_struct_0 @ X0) = (X2))
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '10'])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (![X1 : $i, X2 : $i]:
% 0.75/0.98         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.75/0.98          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.75/0.98          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | ~ (l1_pre_topc @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.98          | ((u1_struct_0 @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.98              = (u1_struct_0 @ X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['6', '12'])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((u1_struct_0 @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.98            = (u1_struct_0 @ X0))
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf(t64_pre_topc, conjecture,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.98                 ( m1_subset_1 @
% 0.75/0.98                   C @ 
% 0.75/0.98                   ( k1_zfmisc_1 @
% 0.75/0.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.98               ( ![D:$i]:
% 0.75/0.98                 ( ( ( v1_funct_1 @ D ) & 
% 0.75/0.98                     ( v1_funct_2 @
% 0.75/0.98                       D @ 
% 0.75/0.98                       ( u1_struct_0 @
% 0.75/0.98                         ( g1_pre_topc @
% 0.75/0.98                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.75/0.98                       ( u1_struct_0 @
% 0.75/0.98                         ( g1_pre_topc @
% 0.75/0.98                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.75/0.98                     ( m1_subset_1 @
% 0.75/0.98                       D @ 
% 0.75/0.98                       ( k1_zfmisc_1 @
% 0.75/0.98                         ( k2_zfmisc_1 @
% 0.75/0.98                           ( u1_struct_0 @
% 0.75/0.98                             ( g1_pre_topc @
% 0.75/0.98                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.75/0.98                           ( u1_struct_0 @
% 0.75/0.98                             ( g1_pre_topc @
% 0.75/0.98                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.75/0.98                   ( ( ( C ) = ( D ) ) =>
% 0.75/0.98                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.75/0.98                       ( v5_pre_topc @
% 0.75/0.98                         D @ 
% 0.75/0.98                         ( g1_pre_topc @
% 0.75/0.98                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.75/0.98                         ( g1_pre_topc @
% 0.75/0.98                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i]:
% 0.75/0.98        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98          ( ![B:$i]:
% 0.75/0.98            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.75/0.98              ( ![C:$i]:
% 0.75/0.98                ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.98                    ( v1_funct_2 @
% 0.75/0.98                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.98                    ( m1_subset_1 @
% 0.75/0.98                      C @ 
% 0.75/0.98                      ( k1_zfmisc_1 @
% 0.75/0.98                        ( k2_zfmisc_1 @
% 0.75/0.98                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.98                  ( ![D:$i]:
% 0.75/0.98                    ( ( ( v1_funct_1 @ D ) & 
% 0.75/0.98                        ( v1_funct_2 @
% 0.75/0.98                          D @ 
% 0.75/0.98                          ( u1_struct_0 @
% 0.75/0.98                            ( g1_pre_topc @
% 0.75/0.98                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.75/0.98                          ( u1_struct_0 @
% 0.75/0.98                            ( g1_pre_topc @
% 0.75/0.98                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.75/0.98                        ( m1_subset_1 @
% 0.75/0.98                          D @ 
% 0.75/0.98                          ( k1_zfmisc_1 @
% 0.75/0.98                            ( k2_zfmisc_1 @
% 0.75/0.98                              ( u1_struct_0 @
% 0.75/0.98                                ( g1_pre_topc @
% 0.75/0.98                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.75/0.98                              ( u1_struct_0 @
% 0.75/0.98                                ( g1_pre_topc @
% 0.75/0.98                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.75/0.98                      ( ( ( C ) = ( D ) ) =>
% 0.75/0.98                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.75/0.98                          ( v5_pre_topc @
% 0.75/0.98                            D @ 
% 0.75/0.98                            ( g1_pre_topc @
% 0.75/0.98                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.75/0.98                            ( g1_pre_topc @
% 0.75/0.98                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ 
% 0.75/0.98          (u1_struct_0 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98          (u1_struct_0 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('19', plain, (((sk_C) = (sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ 
% 0.75/0.98          (u1_struct_0 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98          (u1_struct_0 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.98      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.98  thf(d12_pre_topc, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( l1_pre_topc @ A ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( l1_pre_topc @ B ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.98                 ( m1_subset_1 @
% 0.75/0.98                   C @ 
% 0.75/0.98                   ( k1_zfmisc_1 @
% 0.75/0.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.98               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.75/0.98                 ( ![D:$i]:
% 0.75/0.98                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.75/0.98                     ( ( v4_pre_topc @ D @ B ) =>
% 0.75/0.98                       ( v4_pre_topc @
% 0.75/0.98                         ( k8_relset_1 @
% 0.75/0.98                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.75/0.98                         A ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X5)
% 0.75/0.98          | (m1_subset_1 @ (sk_D @ X6 @ X5 @ X7) @ 
% 0.75/0.98             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.75/0.98          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.98          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.98          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.98          | ~ (v1_funct_1 @ X6)
% 0.75/0.98          | ~ (l1_pre_topc @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.98        | ~ (v1_funct_2 @ sk_C @ 
% 0.75/0.98             (u1_struct_0 @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98             (u1_struct_0 @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (m1_subset_1 @ 
% 0.75/0.98           (sk_D @ sk_C @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98           (k1_zfmisc_1 @ 
% 0.75/0.98            (u1_struct_0 @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98        | ~ (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.98  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      ((v1_funct_2 @ sk_D_1 @ 
% 0.75/0.98        (u1_struct_0 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98        (u1_struct_0 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('25', plain, (((sk_C) = (sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      ((v1_funct_2 @ sk_C @ 
% 0.75/0.98        (u1_struct_0 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98        (u1_struct_0 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (m1_subset_1 @ 
% 0.75/0.98           (sk_D @ sk_C @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98           (k1_zfmisc_1 @ 
% 0.75/0.98            (u1_struct_0 @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98        | ~ (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ~ (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (m1_subset_1 @ 
% 0.75/0.98           (sk_D @ sk_C @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98           (k1_zfmisc_1 @ 
% 0.75/0.98            (u1_struct_0 @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['17', '27'])).
% 0.75/0.98  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (m1_subset_1 @ 
% 0.75/0.98           (sk_D @ sk_C @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98           (k1_zfmisc_1 @ 
% 0.75/0.98            (u1_struct_0 @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('demod', [status(thm)], ['28', '29'])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98         <= (~
% 0.75/0.98             ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('split', [status(esa)], ['31'])).
% 0.75/0.98  thf('33', plain, (((sk_C) = (sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      ((~ (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98         <= (~
% 0.75/0.98             ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('36', plain, (((sk_C) = (sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98         <= (((v5_pre_topc @ sk_C @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('split', [status(esa)], ['37'])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      ((~ (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98         <= (~
% 0.75/0.98             ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (~
% 0.75/0.98       ((v5_pre_topc @ sk_C @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.75/0.98       ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('42', plain, (((sk_C) = (sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      ((~ (v5_pre_topc @ sk_C @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['41', '42'])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      (~
% 0.75/0.98       ((v5_pre_topc @ sk_C @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.75/0.98       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('split', [status(esa)], ['43'])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((u1_struct_0 @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.98            = (u1_struct_0 @ X0))
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((u1_struct_0 @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.98            = (u1_struct_0 @ X0))
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X5)
% 0.75/0.98          | (m1_subset_1 @ (sk_D @ X6 @ X5 @ X7) @ 
% 0.75/0.98             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.75/0.98          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.98          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.98          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.98          | ~ (v1_funct_1 @ X6)
% 0.75/0.98          | ~ (l1_pre_topc @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.98        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.98        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.98        | ~ (l1_pre_topc @ sk_B))),
% 0.75/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.98        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.75/0.98      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.75/0.98  thf(t61_pre_topc, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.75/0.98             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.75/0.98           ( ( v4_pre_topc @
% 0.75/0.98               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.75/0.98             ( m1_subset_1 @
% 0.75/0.98               B @ 
% 0.75/0.98               ( k1_zfmisc_1 @
% 0.75/0.98                 ( u1_struct_0 @
% 0.75/0.98                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X17 : $i, X18 : $i]:
% 0.75/0.98         (~ (v4_pre_topc @ X18 @ X17)
% 0.75/0.98          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.75/0.98          | (v4_pre_topc @ X18 @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.75/0.98          | ~ (l1_pre_topc @ X17)
% 0.75/0.98          | ~ (v2_pre_topc @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.98        | ~ (v2_pre_topc @ sk_B)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_B)
% 0.75/0.98        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.75/0.98      inference('sup-', [status(thm)], ['54', '55'])).
% 0.75/0.98  thf('57', plain, ((v2_pre_topc @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.98        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('61', plain,
% 0.75/0.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X5)
% 0.75/0.98          | (v4_pre_topc @ (sk_D @ X6 @ X5 @ X7) @ X5)
% 0.75/0.98          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.98          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.98          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.98          | ~ (v1_funct_1 @ X6)
% 0.75/0.98          | ~ (l1_pre_topc @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.98        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.98        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.98        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.75/0.98        | ~ (l1_pre_topc @ sk_B))),
% 0.75/0.98      inference('sup-', [status(thm)], ['60', '61'])).
% 0.75/0.98  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.98        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.75/0.98  thf('68', plain,
% 0.75/0.98      (((v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('clc', [status(thm)], ['59', '67'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((u1_struct_0 @ 
% 0.75/0.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.98            = (u1_struct_0 @ X0))
% 0.75/0.98          | ~ (l1_pre_topc @ X0))),
% 0.75/0.98      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf('71', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X0)
% 0.75/0.98          | (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.98  thf('72', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('73', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('split', [status(esa)], ['72'])).
% 0.75/0.98  thf('74', plain, (((sk_C) = (sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('75', plain,
% 0.75/0.98      (((v5_pre_topc @ sk_C @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('demod', [status(thm)], ['73', '74'])).
% 0.75/0.98  thf('76', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C @ 
% 0.75/0.98        (k1_zfmisc_1 @ 
% 0.75/0.98         (k2_zfmisc_1 @ 
% 0.75/0.98          (u1_struct_0 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98          (u1_struct_0 @ 
% 0.75/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.98      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.98  thf('77', plain,
% 0.75/0.98      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ X5)
% 0.75/0.98          | ~ (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.98          | ~ (v4_pre_topc @ X8 @ X5)
% 0.75/0.98          | (v4_pre_topc @ 
% 0.75/0.98             (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ X8) @ 
% 0.75/0.98             X7)
% 0.75/0.98          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.75/0.98          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.98          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.98          | ~ (v1_funct_1 @ X6)
% 0.75/0.98          | ~ (l1_pre_topc @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.98  thf('78', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98          | ~ (v1_funct_1 @ sk_C)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_C @ 
% 0.75/0.98               (u1_struct_0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98               (u1_struct_0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (u1_struct_0 @ 
% 0.75/0.98                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98          | (v4_pre_topc @ 
% 0.75/0.98             (k8_relset_1 @ 
% 0.75/0.98              (u1_struct_0 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98              (u1_struct_0 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.98              sk_C @ X0) @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98          | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98          | ~ (v5_pre_topc @ sk_C @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98          | ~ (l1_pre_topc @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['76', '77'])).
% 0.75/0.98  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('80', plain,
% 0.75/0.98      ((v1_funct_2 @ sk_C @ 
% 0.75/0.98        (u1_struct_0 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98        (u1_struct_0 @ 
% 0.75/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.98  thf('81', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (l1_pre_topc @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (u1_struct_0 @ 
% 0.75/0.98                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98          | (v4_pre_topc @ 
% 0.75/0.98             (k8_relset_1 @ 
% 0.75/0.98              (u1_struct_0 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98              (u1_struct_0 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.98              sk_C @ X0) @ 
% 0.75/0.98             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98          | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98          | ~ (v5_pre_topc @ sk_C @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98          | ~ (l1_pre_topc @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.98      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.75/0.98  thf('82', plain,
% 0.75/0.98      ((![X0 : $i]:
% 0.75/0.98          (~ (l1_pre_topc @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98           | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.98           | (v4_pre_topc @ 
% 0.75/0.98              (k8_relset_1 @ 
% 0.75/0.98               (u1_struct_0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98               (u1_struct_0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.98               sk_C @ X0) @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98           | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.98                (k1_zfmisc_1 @ 
% 0.75/0.98                 (u1_struct_0 @ 
% 0.75/0.98                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98           | ~ (l1_pre_topc @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.75/0.98         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['75', '81'])).
% 0.75/0.98  thf('83', plain,
% 0.75/0.98      ((![X0 : $i]:
% 0.75/0.98          (~ (l1_pre_topc @ sk_B)
% 0.75/0.98           | ~ (l1_pre_topc @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98           | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.98                (k1_zfmisc_1 @ 
% 0.75/0.98                 (u1_struct_0 @ 
% 0.75/0.98                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98           | (v4_pre_topc @ 
% 0.75/0.98              (k8_relset_1 @ 
% 0.75/0.98               (u1_struct_0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.98               (u1_struct_0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.98               sk_C @ X0) @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98           | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.98                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.98         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.98               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['71', '82'])).
% 0.75/0.98  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('85', plain,
% 0.75/0.98      ((![X0 : $i]:
% 0.75/0.98          (~ (l1_pre_topc @ 
% 0.75/0.98              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.98           | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.98                (k1_zfmisc_1 @ 
% 0.75/0.98                 (u1_struct_0 @ 
% 0.75/0.98                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99           | (v4_pre_topc @ 
% 0.75/0.99              (k8_relset_1 @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99               sk_C @ X0) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['83', '84'])).
% 0.75/0.99  thf('86', plain,
% 0.75/0.99      ((![X0 : $i]:
% 0.75/0.99          (~ (l1_pre_topc @ sk_A)
% 0.75/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99           | (v4_pre_topc @ 
% 0.75/0.99              (k8_relset_1 @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99               sk_C @ X0) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99           | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.99                (k1_zfmisc_1 @ 
% 0.75/0.99                 (u1_struct_0 @ 
% 0.75/0.99                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['70', '85'])).
% 0.75/0.99  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('88', plain,
% 0.75/0.99      ((![X0 : $i]:
% 0.75/0.99          (~ (v4_pre_topc @ X0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99           | (v4_pre_topc @ 
% 0.75/0.99              (k8_relset_1 @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99               sk_C @ X0) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99           | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.99                (k1_zfmisc_1 @ 
% 0.75/0.99                 (u1_struct_0 @ 
% 0.75/0.99                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['86', '87'])).
% 0.75/0.99  thf('89', plain,
% 0.75/0.99      ((![X0 : $i]:
% 0.75/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99           | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99           | (v4_pre_topc @ 
% 0.75/0.99              (k8_relset_1 @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99               sk_C @ X0) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['69', '88'])).
% 0.75/0.99  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('91', plain,
% 0.75/0.99      ((![X0 : $i]:
% 0.75/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99           | (v4_pre_topc @ 
% 0.75/0.99              (k8_relset_1 @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99               (u1_struct_0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99               sk_C @ X0) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.75/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['89', '90'])).
% 0.75/0.99  thf('92', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99         | (v4_pre_topc @ 
% 0.75/0.99            (k8_relset_1 @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99         | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.99              (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['68', '91'])).
% 0.75/0.99  thf('93', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.75/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.75/0.99  thf('94', plain,
% 0.75/0.99      ((((v4_pre_topc @ 
% 0.75/0.99          (k8_relset_1 @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('clc', [status(thm)], ['92', '93'])).
% 0.75/0.99  thf('95', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.99      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.99  thf(dt_k8_relset_1, axiom,
% 0.75/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.99       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.99  thf('96', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.75/0.99          | (m1_subset_1 @ (k8_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.75/0.99             (k1_zfmisc_1 @ X1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.75/0.99  thf('97', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (m1_subset_1 @ 
% 0.75/0.99          (k8_relset_1 @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99           sk_C @ X0) @ 
% 0.75/0.99          (k1_zfmisc_1 @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['95', '96'])).
% 0.75/0.99  thf('98', plain,
% 0.75/0.99      (![X16 : $i, X17 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X16 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.75/0.99          | ~ (m1_subset_1 @ X16 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 0.75/0.99          | (v4_pre_topc @ X16 @ X17)
% 0.75/0.99          | ~ (l1_pre_topc @ X17)
% 0.75/0.99          | ~ (v2_pre_topc @ X17))),
% 0.75/0.99      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.75/0.99  thf('99', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v2_pre_topc @ sk_A)
% 0.75/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ 
% 0.75/0.99              (u1_struct_0 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99              (u1_struct_0 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             sk_A)
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99                sk_C @ X0) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['97', '98'])).
% 0.75/0.99  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('102', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((v4_pre_topc @ 
% 0.75/0.99           (k8_relset_1 @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99            sk_C @ X0) @ 
% 0.75/0.99           sk_A)
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99                sk_C @ X0) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.75/0.99      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.75/0.99  thf('103', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99         | (v4_pre_topc @ 
% 0.75/0.99            (k8_relset_1 @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99            sk_A)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['94', '102'])).
% 0.75/0.99  thf('104', plain,
% 0.75/0.99      ((((v4_pre_topc @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99          sk_A)
% 0.75/0.99         | ~ (l1_pre_topc @ sk_A)
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup+', [status(thm)], ['46', '103'])).
% 0.75/0.99  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('106', plain,
% 0.75/0.99      ((((v4_pre_topc @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99          sk_A)
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['104', '105'])).
% 0.75/0.99  thf('107', plain,
% 0.75/0.99      ((((v4_pre_topc @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.99           (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99          sk_A)
% 0.75/0.99         | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup+', [status(thm)], ['45', '106'])).
% 0.75/0.99  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('109', plain,
% 0.75/0.99      ((((v4_pre_topc @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.99           (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.75/0.99          sk_A)
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['107', '108'])).
% 0.75/0.99  thf('110', plain,
% 0.75/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X5)
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ 
% 0.75/0.99                (sk_D @ X6 @ X5 @ X7)) @ 
% 0.75/0.99               X7)
% 0.75/0.99          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.99          | ~ (v1_funct_1 @ X6)
% 0.75/0.99          | ~ (l1_pre_topc @ X7))),
% 0.75/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.99  thf('111', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99         | ~ (l1_pre_topc @ sk_A)
% 0.75/0.99         | ~ (v1_funct_1 @ sk_C)
% 0.75/0.99         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.99         | ~ (m1_subset_1 @ sk_C @ 
% 0.75/0.99              (k1_zfmisc_1 @ 
% 0.75/0.99               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99         | ~ (l1_pre_topc @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['109', '110'])).
% 0.75/0.99  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('114', plain,
% 0.75/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('115', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('117', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)],
% 0.75/0.99                ['111', '112', '113', '114', '115', '116'])).
% 0.75/0.99  thf('118', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('simplify', [status(thm)], ['117'])).
% 0.75/0.99  thf('119', plain,
% 0.75/0.99      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.75/0.99         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.75/0.99      inference('split', [status(esa)], ['31'])).
% 0.75/0.99  thf('120', plain,
% 0.75/0.99      (~
% 0.75/0.99       ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.75/0.99       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.99      inference('sup-', [status(thm)], ['118', '119'])).
% 0.75/0.99  thf('121', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['73', '74'])).
% 0.75/0.99  thf('122', plain,
% 0.75/0.99      ((~ (v5_pre_topc @ sk_C @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.99         <= (~
% 0.75/0.99             ((v5_pre_topc @ sk_C @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('split', [status(esa)], ['43'])).
% 0.75/0.99  thf('123', plain,
% 0.75/0.99      (~
% 0.75/0.99       ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.75/0.99       ((v5_pre_topc @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['121', '122'])).
% 0.75/0.99  thf('124', plain,
% 0.75/0.99      (~
% 0.75/0.99       ((v5_pre_topc @ sk_D_1 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sat_resolution*', [status(thm)], ['40', '44', '120', '123'])).
% 0.75/0.99  thf('125', plain,
% 0.75/0.99      (~ (v5_pre_topc @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.75/0.99      inference('simpl_trail', [status(thm)], ['34', '124'])).
% 0.75/0.99  thf('126', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99         (k1_zfmisc_1 @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('clc', [status(thm)], ['30', '125'])).
% 0.75/0.99  thf('127', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | (m1_subset_1 @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (k1_zfmisc_1 @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['16', '126'])).
% 0.75/0.99  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('129', plain,
% 0.75/0.99      ((m1_subset_1 @ 
% 0.75/0.99        (sk_D @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (u1_struct_0 @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['127', '128'])).
% 0.75/0.99  thf('130', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ sk_B))),
% 0.75/0.99      inference('sup+', [status(thm)], ['15', '129'])).
% 0.75/0.99  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('132', plain,
% 0.75/0.99      ((m1_subset_1 @ 
% 0.75/0.99        (sk_D @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.99      inference('demod', [status(thm)], ['130', '131'])).
% 0.75/0.99  thf('133', plain,
% 0.75/0.99      (![X17 : $i, X18 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X18 @ X17)
% 0.75/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.75/0.99          | (v4_pre_topc @ X18 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.75/0.99          | ~ (l1_pre_topc @ X17)
% 0.75/0.99          | ~ (v2_pre_topc @ X17))),
% 0.75/0.99      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.75/0.99  thf('134', plain,
% 0.75/0.99      ((~ (v2_pre_topc @ sk_B)
% 0.75/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (v4_pre_topc @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             sk_B))),
% 0.75/0.99      inference('sup-', [status(thm)], ['132', '133'])).
% 0.75/0.99  thf('135', plain, ((v2_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('136', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('137', plain,
% 0.75/0.99      (((v4_pre_topc @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (v4_pre_topc @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             sk_B))),
% 0.75/0.99      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.75/0.99  thf('138', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X0)
% 0.75/0.99          | (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf('139', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X0)
% 0.75/0.99          | (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf('140', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.99      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.99  thf('141', plain,
% 0.75/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X5)
% 0.75/0.99          | (v4_pre_topc @ (sk_D @ X6 @ X5 @ X7) @ X5)
% 0.75/0.99          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.99          | ~ (v1_funct_1 @ X6)
% 0.75/0.99          | ~ (l1_pre_topc @ X7))),
% 0.75/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.99  thf('142', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.99        | ~ (v1_funct_2 @ sk_C @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['140', '141'])).
% 0.75/0.99  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('144', plain,
% 0.75/0.99      ((v1_funct_2 @ sk_C @ 
% 0.75/0.99        (u1_struct_0 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        (u1_struct_0 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.99  thf('145', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.75/0.99  thf('146', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['139', '145'])).
% 0.75/0.99  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('148', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['146', '147'])).
% 0.75/0.99  thf('149', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | (v5_pre_topc @ sk_C @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['138', '148'])).
% 0.75/0.99  thf('150', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('151', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['149', '150'])).
% 0.75/0.99  thf('152', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('153', plain,
% 0.75/0.99      (![X16 : $i, X17 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X16 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.75/0.99          | ~ (m1_subset_1 @ X16 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 0.75/0.99          | (v4_pre_topc @ X16 @ X17)
% 0.75/0.99          | ~ (l1_pre_topc @ X17)
% 0.75/0.99          | ~ (v2_pre_topc @ X17))),
% 0.75/0.99      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.75/0.99  thf('154', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i]:
% 0.75/0.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.75/0.99          | ~ (l1_pre_topc @ X0)
% 0.75/0.99          | ~ (v2_pre_topc @ X0)
% 0.75/0.99          | ~ (l1_pre_topc @ X0)
% 0.75/0.99          | (v4_pre_topc @ X1 @ X0)
% 0.75/0.99          | ~ (v4_pre_topc @ X1 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['152', '153'])).
% 0.75/0.99  thf('155', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X1 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99          | (v4_pre_topc @ X1 @ X0)
% 0.75/0.99          | ~ (v2_pre_topc @ X0)
% 0.75/0.99          | ~ (l1_pre_topc @ X0)
% 0.75/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.75/0.99      inference('simplify', [status(thm)], ['154'])).
% 0.75/0.99  thf('156', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (m1_subset_1 @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | ~ (v2_pre_topc @ sk_B)
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           sk_B))),
% 0.75/0.99      inference('sup-', [status(thm)], ['151', '155'])).
% 0.75/0.99  thf('157', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('158', plain, ((v2_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('159', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (m1_subset_1 @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           sk_B))),
% 0.75/0.99      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.75/0.99  thf('160', plain,
% 0.75/0.99      ((m1_subset_1 @ 
% 0.75/0.99        (sk_D @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.99      inference('demod', [status(thm)], ['130', '131'])).
% 0.75/0.99  thf('161', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           sk_B))),
% 0.75/0.99      inference('demod', [status(thm)], ['159', '160'])).
% 0.75/0.99  thf('162', plain,
% 0.75/0.99      (~ (v5_pre_topc @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.75/0.99      inference('simpl_trail', [status(thm)], ['34', '124'])).
% 0.75/0.99  thf('163', plain,
% 0.75/0.99      ((v4_pre_topc @ 
% 0.75/0.99        (sk_D @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        sk_B)),
% 0.75/0.99      inference('clc', [status(thm)], ['161', '162'])).
% 0.75/0.99  thf('164', plain,
% 0.75/0.99      ((v4_pre_topc @ 
% 0.75/0.99        (sk_D @ sk_C @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.75/0.99      inference('demod', [status(thm)], ['137', '163'])).
% 0.75/0.99  thf('165', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('166', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X0)
% 0.75/0.99          | (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf('167', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X0)
% 0.75/0.99          | (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf('168', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('169', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X0)
% 0.75/0.99          | (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf('170', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('171', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.99      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.99  thf('172', plain,
% 0.75/0.99      (((m1_subset_1 @ sk_C @ 
% 0.75/0.99         (k1_zfmisc_1 @ 
% 0.75/0.99          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.75/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.99      inference('sup+', [status(thm)], ['170', '171'])).
% 0.75/0.99  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('174', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.99      inference('demod', [status(thm)], ['172', '173'])).
% 0.75/0.99  thf('175', plain,
% 0.75/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X5)
% 0.75/0.99          | (m1_subset_1 @ (sk_D @ X6 @ X5 @ X7) @ 
% 0.75/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.75/0.99          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.99          | ~ (v1_funct_1 @ X6)
% 0.75/0.99          | ~ (l1_pre_topc @ X7))),
% 0.75/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.99  thf('176', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (m1_subset_1 @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           (k1_zfmisc_1 @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['174', '175'])).
% 0.75/0.99  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('179', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('180', plain,
% 0.75/0.99      ((v1_funct_2 @ sk_C @ 
% 0.75/0.99        (u1_struct_0 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99        (u1_struct_0 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.99  thf('181', plain,
% 0.75/0.99      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99         (u1_struct_0 @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.99      inference('sup+', [status(thm)], ['179', '180'])).
% 0.75/0.99  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('183', plain,
% 0.75/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99        (u1_struct_0 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['181', '182'])).
% 0.75/0.99  thf('184', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (m1_subset_1 @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           (k1_zfmisc_1 @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['176', '177', '178', '183'])).
% 0.75/0.99  thf('185', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | (m1_subset_1 @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           (k1_zfmisc_1 @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['169', '184'])).
% 0.75/0.99  thf('186', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('187', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99         (k1_zfmisc_1 @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['185', '186'])).
% 0.75/0.99  thf('188', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup+', [status(thm)], ['168', '187'])).
% 0.75/0.99  thf('189', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('190', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['188', '189'])).
% 0.75/0.99  thf('191', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.75/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.75/0.99      inference('split', [status(esa)], ['72'])).
% 0.75/0.99  thf('192', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('193', plain,
% 0.75/0.99      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X5)
% 0.75/0.99          | ~ (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.99          | ~ (v4_pre_topc @ X8 @ X5)
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ X8) @ 
% 0.75/0.99             X7)
% 0.75/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.75/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.99          | ~ (v1_funct_1 @ X6)
% 0.75/0.99          | ~ (l1_pre_topc @ X7))),
% 0.75/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.99  thf('194', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ sk_A)
% 0.75/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.75/0.99          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             sk_A)
% 0.75/0.99          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.75/0.99          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.75/0.99          | ~ (l1_pre_topc @ sk_B))),
% 0.75/0.99      inference('sup-', [status(thm)], ['192', '193'])).
% 0.75/0.99  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('197', plain,
% 0.75/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('198', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('199', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             sk_A)
% 0.75/0.99          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.75/0.99          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.75/0.99      inference('demod', [status(thm)], ['194', '195', '196', '197', '198'])).
% 0.75/0.99  thf('200', plain,
% 0.75/0.99      ((![X0 : $i]:
% 0.75/0.99          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.75/0.99           | (v4_pre_topc @ 
% 0.75/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99               sk_C @ X0) @ 
% 0.75/0.99              sk_A)
% 0.75/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['191', '199'])).
% 0.75/0.99  thf('201', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99         | (v4_pre_topc @ 
% 0.75/0.99            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99             sk_C @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              sk_A)) @ 
% 0.75/0.99            sk_A)
% 0.75/0.99         | ~ (v4_pre_topc @ 
% 0.75/0.99              (sk_D @ sk_C @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99               sk_A) @ 
% 0.75/0.99              sk_B)))
% 0.75/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['190', '200'])).
% 0.75/0.99  thf('202', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['188', '189'])).
% 0.75/0.99  thf('203', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X0)
% 0.75/0.99          | (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf('204', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99          (u1_struct_0 @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.75/0.99      inference('demod', [status(thm)], ['172', '173'])).
% 0.75/0.99  thf('205', plain,
% 0.75/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.99         (~ (l1_pre_topc @ X5)
% 0.75/0.99          | (v4_pre_topc @ (sk_D @ X6 @ X5 @ X7) @ X5)
% 0.75/0.99          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.75/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.75/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.75/0.99          | ~ (v1_funct_1 @ X6)
% 0.75/0.99          | ~ (l1_pre_topc @ X7))),
% 0.75/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.75/0.99  thf('206', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99             (u1_struct_0 @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['204', '205'])).
% 0.75/0.99  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('209', plain,
% 0.75/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99        (u1_struct_0 @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['181', '182'])).
% 0.75/0.99  thf('210', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 0.75/0.99  thf('211', plain,
% 0.75/0.99      ((~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['203', '210'])).
% 0.75/0.99  thf('212', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('213', plain,
% 0.75/0.99      (((v4_pre_topc @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('demod', [status(thm)], ['211', '212'])).
% 0.75/0.99  thf('214', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X1 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99          | (v4_pre_topc @ X1 @ X0)
% 0.75/0.99          | ~ (v2_pre_topc @ X0)
% 0.75/0.99          | ~ (l1_pre_topc @ X0)
% 0.75/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.75/0.99      inference('simplify', [status(thm)], ['154'])).
% 0.75/0.99  thf('215', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (m1_subset_1 @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              sk_A) @ 
% 0.75/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99        | ~ (v2_pre_topc @ sk_B)
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           sk_B))),
% 0.75/0.99      inference('sup-', [status(thm)], ['213', '214'])).
% 0.75/0.99  thf('216', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('217', plain, ((v2_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('218', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | ~ (m1_subset_1 @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              sk_A) @ 
% 0.75/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           sk_B))),
% 0.75/0.99      inference('demod', [status(thm)], ['215', '216', '217'])).
% 0.75/0.99  thf('219', plain,
% 0.75/0.99      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99        | (v4_pre_topc @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99           sk_B)
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['202', '218'])).
% 0.75/0.99  thf('220', plain,
% 0.75/0.99      (((v4_pre_topc @ 
% 0.75/0.99         (sk_D @ sk_C @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.75/0.99         sk_B)
% 0.75/0.99        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.75/0.99      inference('simplify', [status(thm)], ['219'])).
% 0.75/0.99  thf('221', plain,
% 0.75/0.99      ((((v4_pre_topc @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.99           (sk_D @ sk_C @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.75/0.99          sk_A)
% 0.75/0.99         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.75/0.99      inference('clc', [status(thm)], ['201', '220'])).
% 0.75/0.99  thf('222', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_C @ 
% 0.75/0.99        (k1_zfmisc_1 @ 
% 0.75/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('223', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.75/0.99          | (m1_subset_1 @ (k8_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.75/0.99             (k1_zfmisc_1 @ X1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.75/0.99  thf('224', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (m1_subset_1 @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.99           X0) @ 
% 0.75/0.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['222', '223'])).
% 0.75/0.99  thf('225', plain,
% 0.75/0.99      (![X17 : $i, X18 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X18 @ X17)
% 0.75/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.75/0.99          | (v4_pre_topc @ X18 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.75/0.99          | ~ (l1_pre_topc @ X17)
% 0.75/0.99          | ~ (v2_pre_topc @ X17))),
% 0.75/0.99      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.75/0.99  thf('226', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v2_pre_topc @ sk_A)
% 0.75/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99                sk_C @ X0) @ 
% 0.75/0.99               sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['224', '225'])).
% 0.75/0.99  thf('227', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('229', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((v4_pre_topc @ 
% 0.75/0.99           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.99            X0) @ 
% 0.75/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99                sk_C @ X0) @ 
% 0.75/0.99               sk_A))),
% 0.75/0.99      inference('demod', [status(thm)], ['226', '227', '228'])).
% 0.75/0.99  thf('230', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99         | (v4_pre_topc @ 
% 0.75/0.99            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99             sk_C @ 
% 0.75/0.99             (sk_D @ sk_C @ 
% 0.75/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.75/0.99              sk_A)) @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.75/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['221', '229'])).
% 0.75/0.99  thf('231', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('232', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/0.99            = (u1_struct_0 @ X0))
% 0.75/0.99          | ~ (l1_pre_topc @ X0))),
% 0.75/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('233', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (m1_subset_1 @ 
% 0.75/0.99          (k8_relset_1 @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99           sk_C @ X0) @ 
% 0.75/0.99          (k1_zfmisc_1 @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['95', '96'])).
% 0.75/0.99  thf('234', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((m1_subset_1 @ 
% 0.75/0.99           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99            sk_C @ X0) @ 
% 0.75/0.99           (k1_zfmisc_1 @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.75/0.99          | ~ (l1_pre_topc @ sk_A))),
% 0.75/0.99      inference('sup+', [status(thm)], ['232', '233'])).
% 0.75/0.99  thf('235', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('236', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (m1_subset_1 @ 
% 0.75/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99           sk_C @ X0) @ 
% 0.75/0.99          (k1_zfmisc_1 @ 
% 0.75/0.99           (u1_struct_0 @ 
% 0.75/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['234', '235'])).
% 0.75/0.99  thf('237', plain,
% 0.75/0.99      (![X16 : $i, X17 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ X16 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.75/0.99          | ~ (m1_subset_1 @ X16 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 0.75/0.99          | (v4_pre_topc @ X16 @ X17)
% 0.75/0.99          | ~ (l1_pre_topc @ X17)
% 0.75/0.99          | ~ (v2_pre_topc @ X17))),
% 0.75/0.99      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.75/0.99  thf('238', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v2_pre_topc @ sk_A)
% 0.75/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99              (u1_struct_0 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             sk_A)
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99                sk_C @ X0) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['236', '237'])).
% 0.75/0.99  thf('239', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('241', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((v4_pre_topc @ 
% 0.75/0.99           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99            (u1_struct_0 @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99            sk_C @ X0) @ 
% 0.75/0.99           sk_A)
% 0.75/0.99          | ~ (v4_pre_topc @ 
% 0.75/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99                (u1_struct_0 @ 
% 0.75/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99                sk_C @ X0) @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.75/0.99      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.75/0.99  thf('242', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99              (u1_struct_0 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['231', '241'])).
% 0.75/0.99  thf('243', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('244', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.75/0.99          | (v4_pre_topc @ 
% 0.75/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.99              (u1_struct_0 @ 
% 0.75/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.75/0.99              sk_C @ X0) @ 
% 0.75/0.99             sk_A))),
% 0.75/0.99      inference('demod', [status(thm)], ['242', '243'])).
% 0.75/0.99  thf('245', plain,
% 0.75/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.75/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.75/0.99         | (v4_pre_topc @ 
% 0.82/0.99            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99             (u1_struct_0 @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99             sk_C @ 
% 0.82/0.99             (sk_D @ sk_C @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.82/0.99              sk_A)) @ 
% 0.82/0.99            sk_A)))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['230', '244'])).
% 0.82/0.99  thf('246', plain,
% 0.82/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.82/0.99         (~ (l1_pre_topc @ X5)
% 0.82/0.99          | ~ (v4_pre_topc @ 
% 0.82/0.99               (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ 
% 0.82/0.99                (sk_D @ X6 @ X5 @ X7)) @ 
% 0.82/0.99               X7)
% 0.82/0.99          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.82/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.82/0.99               (k1_zfmisc_1 @ 
% 0.82/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.82/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.82/0.99          | ~ (v1_funct_1 @ X6)
% 0.82/0.99          | ~ (l1_pre_topc @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.82/0.99  thf('247', plain,
% 0.82/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99         | ~ (l1_pre_topc @ sk_A)
% 0.82/0.99         | ~ (v1_funct_1 @ sk_C)
% 0.82/0.99         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99              (u1_struct_0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.82/0.99         | ~ (m1_subset_1 @ sk_C @ 
% 0.82/0.99              (k1_zfmisc_1 @ 
% 0.82/0.99               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99                (u1_struct_0 @ 
% 0.82/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.82/0.99         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99         | ~ (l1_pre_topc @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['245', '246'])).
% 0.82/0.99  thf('248', plain, ((l1_pre_topc @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('249', plain, ((v1_funct_1 @ sk_C)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('250', plain,
% 0.82/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99        (u1_struct_0 @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('demod', [status(thm)], ['181', '182'])).
% 0.82/0.99  thf('251', plain,
% 0.82/0.99      ((m1_subset_1 @ sk_C @ 
% 0.82/0.99        (k1_zfmisc_1 @ 
% 0.82/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99          (u1_struct_0 @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.82/0.99      inference('demod', [status(thm)], ['172', '173'])).
% 0.82/0.99  thf('252', plain,
% 0.82/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99         | ~ (l1_pre_topc @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('demod', [status(thm)], ['247', '248', '249', '250', '251'])).
% 0.82/0.99  thf('253', plain,
% 0.82/0.99      (((~ (l1_pre_topc @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['252'])).
% 0.82/0.99  thf('254', plain,
% 0.82/0.99      (((~ (l1_pre_topc @ sk_B)
% 0.82/0.99         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['167', '253'])).
% 0.82/0.99  thf('255', plain, ((l1_pre_topc @ sk_B)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('256', plain,
% 0.82/0.99      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('demod', [status(thm)], ['254', '255'])).
% 0.82/0.99  thf('257', plain,
% 0.82/0.99      ((m1_subset_1 @ sk_C @ 
% 0.82/0.99        (k1_zfmisc_1 @ 
% 0.82/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99          (u1_struct_0 @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.82/0.99      inference('demod', [status(thm)], ['172', '173'])).
% 0.82/0.99  thf('258', plain,
% 0.82/0.99      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/0.99         (~ (l1_pre_topc @ X5)
% 0.82/0.99          | ~ (v5_pre_topc @ X6 @ X7 @ X5)
% 0.82/0.99          | ~ (v4_pre_topc @ X8 @ X5)
% 0.82/0.99          | (v4_pre_topc @ 
% 0.82/0.99             (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ X8) @ 
% 0.82/0.99             X7)
% 0.82/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.82/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.82/0.99               (k1_zfmisc_1 @ 
% 0.82/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.82/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.82/0.99          | ~ (v1_funct_1 @ X6)
% 0.82/0.99          | ~ (l1_pre_topc @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.82/0.99  thf('259', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_pre_topc @ sk_A)
% 0.82/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.82/0.99          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.82/0.99          | ~ (m1_subset_1 @ X0 @ 
% 0.82/0.99               (k1_zfmisc_1 @ 
% 0.82/0.99                (u1_struct_0 @ 
% 0.82/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99          | (v4_pre_topc @ 
% 0.82/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99              (u1_struct_0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99              sk_C @ X0) @ 
% 0.82/0.99             sk_A)
% 0.82/0.99          | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99          | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99          | ~ (l1_pre_topc @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['257', '258'])).
% 0.82/0.99  thf('260', plain, ((l1_pre_topc @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('261', plain, ((v1_funct_1 @ sk_C)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('262', plain,
% 0.82/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99        (u1_struct_0 @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('demod', [status(thm)], ['181', '182'])).
% 0.82/0.99  thf('263', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (m1_subset_1 @ X0 @ 
% 0.82/0.99             (k1_zfmisc_1 @ 
% 0.82/0.99              (u1_struct_0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99          | (v4_pre_topc @ 
% 0.82/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99              (u1_struct_0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99              sk_C @ X0) @ 
% 0.82/0.99             sk_A)
% 0.82/0.99          | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99          | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99          | ~ (l1_pre_topc @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 0.82/0.99  thf('264', plain,
% 0.82/0.99      ((![X0 : $i]:
% 0.82/0.99          (~ (l1_pre_topc @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99           | (v4_pre_topc @ 
% 0.82/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99               sk_C @ X0) @ 
% 0.82/0.99              sk_A)
% 0.82/0.99           | ~ (m1_subset_1 @ X0 @ 
% 0.82/0.99                (k1_zfmisc_1 @ 
% 0.82/0.99                 (u1_struct_0 @ 
% 0.82/0.99                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['256', '263'])).
% 0.82/0.99  thf('265', plain,
% 0.82/0.99      ((![X0 : $i]:
% 0.82/0.99          (~ (l1_pre_topc @ sk_B)
% 0.82/0.99           | ~ (m1_subset_1 @ X0 @ 
% 0.82/0.99                (k1_zfmisc_1 @ 
% 0.82/0.99                 (u1_struct_0 @ 
% 0.82/0.99                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99           | (v4_pre_topc @ 
% 0.82/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99               sk_C @ X0) @ 
% 0.82/0.99              sk_A)
% 0.82/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['166', '264'])).
% 0.82/0.99  thf('266', plain, ((l1_pre_topc @ sk_B)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('267', plain,
% 0.82/0.99      ((![X0 : $i]:
% 0.82/0.99          (~ (m1_subset_1 @ X0 @ 
% 0.82/0.99              (k1_zfmisc_1 @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99           | (v4_pre_topc @ 
% 0.82/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99               sk_C @ X0) @ 
% 0.82/0.99              sk_A)
% 0.82/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('demod', [status(thm)], ['265', '266'])).
% 0.82/0.99  thf('268', plain,
% 0.82/0.99      ((![X0 : $i]:
% 0.82/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.82/0.99           | ~ (l1_pre_topc @ sk_B)
% 0.82/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99           | (v4_pre_topc @ 
% 0.82/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99               sk_C @ X0) @ 
% 0.82/0.99              sk_A)))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['165', '267'])).
% 0.82/0.99  thf('269', plain, ((l1_pre_topc @ sk_B)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('270', plain,
% 0.82/0.99      ((![X0 : $i]:
% 0.82/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.82/0.99           | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99           | (v4_pre_topc @ 
% 0.82/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99               sk_C @ X0) @ 
% 0.82/0.99              sk_A)))
% 0.82/0.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.82/0.99      inference('demod', [status(thm)], ['268', '269'])).
% 0.82/0.99  thf('271', plain,
% 0.82/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.82/0.99       ((v5_pre_topc @ sk_C @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('split', [status(esa)], ['37'])).
% 0.82/0.99  thf('272', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.82/0.99      inference('sat_resolution*', [status(thm)], ['40', '44', '120', '271'])).
% 0.82/0.99  thf('273', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.82/0.99          | ~ (v4_pre_topc @ X0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99          | (v4_pre_topc @ 
% 0.82/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99              (u1_struct_0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99              sk_C @ X0) @ 
% 0.82/0.99             sk_A))),
% 0.82/0.99      inference('simpl_trail', [status(thm)], ['270', '272'])).
% 0.82/0.99  thf('274', plain,
% 0.82/0.99      (((v4_pre_topc @ 
% 0.82/0.99         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99          (u1_struct_0 @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99          sk_C @ 
% 0.82/0.99          (sk_D @ sk_C @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.82/0.99         sk_A)
% 0.82/0.99        | ~ (m1_subset_1 @ 
% 0.82/0.99             (sk_D @ sk_C @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.82/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['164', '273'])).
% 0.82/0.99  thf('275', plain,
% 0.82/0.99      ((m1_subset_1 @ 
% 0.82/0.99        (sk_D @ sk_C @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.82/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.82/0.99      inference('demod', [status(thm)], ['130', '131'])).
% 0.82/0.99  thf('276', plain,
% 0.82/0.99      ((v4_pre_topc @ 
% 0.82/0.99        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99         (u1_struct_0 @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99         sk_C @ 
% 0.82/0.99         (sk_D @ sk_C @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.82/0.99        sk_A)),
% 0.82/0.99      inference('demod', [status(thm)], ['274', '275'])).
% 0.82/0.99  thf('277', plain,
% 0.82/0.99      ((m1_subset_1 @ sk_C @ 
% 0.82/0.99        (k1_zfmisc_1 @ 
% 0.82/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99          (u1_struct_0 @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.82/0.99      inference('demod', [status(thm)], ['172', '173'])).
% 0.82/0.99  thf('278', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.82/0.99          | (m1_subset_1 @ (k8_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.82/0.99             (k1_zfmisc_1 @ X1)))),
% 0.82/0.99      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.82/0.99  thf('279', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (m1_subset_1 @ 
% 0.82/0.99          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99           (u1_struct_0 @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99           sk_C @ X0) @ 
% 0.82/0.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['277', '278'])).
% 0.82/0.99  thf('280', plain,
% 0.82/0.99      (![X17 : $i, X18 : $i]:
% 0.82/0.99         (~ (v4_pre_topc @ X18 @ X17)
% 0.82/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.82/0.99          | (v4_pre_topc @ X18 @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.82/0.99          | ~ (l1_pre_topc @ X17)
% 0.82/0.99          | ~ (v2_pre_topc @ X17))),
% 0.82/0.99      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.82/0.99  thf('281', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (v2_pre_topc @ sk_A)
% 0.82/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.82/0.99          | (v4_pre_topc @ 
% 0.82/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99              (u1_struct_0 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99              sk_C @ X0) @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.82/0.99          | ~ (v4_pre_topc @ 
% 0.82/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99                (u1_struct_0 @ 
% 0.82/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99                sk_C @ X0) @ 
% 0.82/0.99               sk_A))),
% 0.82/0.99      inference('sup-', [status(thm)], ['279', '280'])).
% 0.82/0.99  thf('282', plain, ((v2_pre_topc @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('283', plain, ((l1_pre_topc @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('284', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((v4_pre_topc @ 
% 0.82/0.99           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99            (u1_struct_0 @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99            sk_C @ X0) @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.82/0.99          | ~ (v4_pre_topc @ 
% 0.82/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99                (u1_struct_0 @ 
% 0.82/0.99                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99                sk_C @ X0) @ 
% 0.82/0.99               sk_A))),
% 0.82/0.99      inference('demod', [status(thm)], ['281', '282', '283'])).
% 0.82/0.99  thf('285', plain,
% 0.82/0.99      ((v4_pre_topc @ 
% 0.82/0.99        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.82/0.99         (u1_struct_0 @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.82/0.99         sk_C @ 
% 0.82/0.99         (sk_D @ sk_C @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.82/0.99        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['276', '284'])).
% 0.82/0.99  thf('286', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((u1_struct_0 @ 
% 0.82/0.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.82/0.99            = (u1_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_pre_topc @ X0))),
% 0.82/0.99      inference('clc', [status(thm)], ['13', '14'])).
% 0.82/0.99  thf('287', plain,
% 0.82/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.82/0.99         (~ (l1_pre_topc @ X5)
% 0.82/0.99          | ~ (v4_pre_topc @ 
% 0.82/0.99               (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ 
% 0.82/0.99                (sk_D @ X6 @ X5 @ X7)) @ 
% 0.82/0.99               X7)
% 0.82/0.99          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.82/0.99          | ~ (m1_subset_1 @ X6 @ 
% 0.82/0.99               (k1_zfmisc_1 @ 
% 0.82/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.82/0.99          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.82/0.99          | ~ (v1_funct_1 @ X6)
% 0.82/0.99          | ~ (l1_pre_topc @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.82/0.99  thf('288', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/0.99         (~ (v4_pre_topc @ 
% 0.82/0.99             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 0.82/0.99              (sk_D @ X2 @ X1 @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.82/0.99          | ~ (l1_pre_topc @ X0)
% 0.82/0.99          | ~ (l1_pre_topc @ 
% 0.82/0.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.82/0.99          | ~ (v1_funct_1 @ X2)
% 0.82/0.99          | ~ (v1_funct_2 @ X2 @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.82/0.99               (u1_struct_0 @ X1))
% 0.82/0.99          | ~ (m1_subset_1 @ X2 @ 
% 0.82/0.99               (k1_zfmisc_1 @ 
% 0.82/0.99                (k2_zfmisc_1 @ 
% 0.82/0.99                 (u1_struct_0 @ 
% 0.82/0.99                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.82/0.99                 (u1_struct_0 @ X1))))
% 0.82/0.99          | (v5_pre_topc @ X2 @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.82/0.99          | ~ (l1_pre_topc @ X1))),
% 0.82/0.99      inference('sup-', [status(thm)], ['286', '287'])).
% 0.82/0.99  thf('289', plain,
% 0.82/0.99      ((~ (l1_pre_topc @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99        | (v5_pre_topc @ sk_C @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99        | ~ (m1_subset_1 @ sk_C @ 
% 0.82/0.99             (k1_zfmisc_1 @ 
% 0.82/0.99              (k2_zfmisc_1 @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.82/0.99               (u1_struct_0 @ 
% 0.82/0.99                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.82/0.99        | ~ (v1_funct_2 @ sk_C @ 
% 0.82/0.99             (u1_struct_0 @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.82/0.99             (u1_struct_0 @ 
% 0.82/0.99              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.82/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.82/0.99        | ~ (l1_pre_topc @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.82/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.82/0.99      inference('sup-', [status(thm)], ['285', '288'])).
% 0.82/0.99  thf('290', plain,
% 0.82/0.99      ((m1_subset_1 @ sk_C @ 
% 0.82/0.99        (k1_zfmisc_1 @ 
% 0.82/0.99         (k2_zfmisc_1 @ 
% 0.82/0.99          (u1_struct_0 @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.82/0.99          (u1_struct_0 @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.82/0.99      inference('demod', [status(thm)], ['18', '19'])).
% 0.82/0.99  thf('291', plain,
% 0.82/0.99      ((v1_funct_2 @ sk_C @ 
% 0.82/0.99        (u1_struct_0 @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.82/0.99        (u1_struct_0 @ 
% 0.82/0.99         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.82/0.99  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('293', plain, ((l1_pre_topc @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('294', plain,
% 0.82/0.99      ((~ (l1_pre_topc @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99        | (v5_pre_topc @ sk_C @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.82/0.99        | ~ (l1_pre_topc @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.82/0.99      inference('demod', [status(thm)], ['289', '290', '291', '292', '293'])).
% 0.82/0.99  thf('295', plain,
% 0.82/0.99      (~ (v5_pre_topc @ sk_C @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.82/0.99      inference('simpl_trail', [status(thm)], ['34', '124'])).
% 0.82/0.99  thf('296', plain,
% 0.82/0.99      ((~ (l1_pre_topc @ 
% 0.82/0.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.82/0.99        | ~ (l1_pre_topc @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('clc', [status(thm)], ['294', '295'])).
% 0.82/0.99  thf('297', plain,
% 0.82/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.82/0.99        | ~ (l1_pre_topc @ 
% 0.82/0.99             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['3', '296'])).
% 0.82/0.99  thf('298', plain, ((l1_pre_topc @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('299', plain,
% 0.82/0.99      (~ (l1_pre_topc @ 
% 0.82/0.99          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.82/0.99      inference('demod', [status(thm)], ['297', '298'])).
% 0.82/0.99  thf('300', plain, (~ (l1_pre_topc @ sk_B)),
% 0.82/0.99      inference('sup-', [status(thm)], ['2', '299'])).
% 0.82/0.99  thf('301', plain, ((l1_pre_topc @ sk_B)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('302', plain, ($false), inference('demod', [status(thm)], ['300', '301'])).
% 0.82/0.99  
% 0.82/0.99  % SZS output end Refutation
% 0.82/0.99  
% 0.82/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
