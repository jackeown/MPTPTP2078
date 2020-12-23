%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n6s0rCRvva

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:28 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  262 (3111 expanded)
%              Number of leaves         :   27 ( 928 expanded)
%              Depth                    :   41
%              Number of atoms          : 4944 (87144 expanded)
%              Number of equality atoms :   33 (1712 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
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
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_pre_topc @ X10 @ X11 )
       != ( g1_pre_topc @ X8 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
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
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X3 ) @ X1 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','58'])).

thf('60',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('63',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t62_pre_topc,axiom,(
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

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v5_pre_topc @ X18 @ X17 @ X15 )
      | ( v5_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) @ X15 )
      | ( X18 != X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('71',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ( v5_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) @ X15 )
      | ~ ( v5_pre_topc @ X16 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75','80','81','82','83','84'])).

thf('86',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('88',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( v4_pre_topc @ X4 @ X1 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['100'])).

thf('102',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','105'])).

thf('107',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('116',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('120',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['114','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('126',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('132',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X3 ) @ X1 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('133',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('136',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['129','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('145',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('146',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('149',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( v4_pre_topc @ X4 @ X1 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['147','153'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['144','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['143','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','163'])).

thf('165',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('166',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['112','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('174',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X3 ) ) @ X3 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('179',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180','181'])).

thf('183',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['111','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('188',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v5_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) @ X15 )
      | ( v5_pre_topc @ X18 @ X17 @ X15 )
      | ( X18 != X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('189',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ( v5_pre_topc @ X16 @ X17 @ X15 )
      | ~ ( v5_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['187','189'])).

thf('191',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['190','191','192','193','194','195','196','197','198'])).

thf('200',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['186','199'])).

thf('201',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['102'])).

thf('202',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['100'])).

thf('204',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['106','110','202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['97','204'])).

thf('206',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','205'])).

thf('207',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('208',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('209',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['109'])).

thf('210',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['106','110','202','210'])).

thf('212',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['207','211'])).

thf('213',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['206','212'])).

thf('214',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','213'])).

thf('215',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['207','211'])).

thf('216',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('218',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X3 ) ) @ X3 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('219',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 @ ( sk_D @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( v5_pre_topc @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('222',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['220','221','222','223','224'])).

thf('226',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['207','211'])).

thf('227',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','227'])).

thf('229',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['2','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    $false ),
    inference(demod,[status(thm)],['231','232'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n6s0rCRvva
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.95/1.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.95/1.23  % Solved by: fo/fo7.sh
% 0.95/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.95/1.23  % done 897 iterations in 0.765s
% 0.95/1.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.95/1.23  % SZS output start Refutation
% 0.95/1.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.95/1.23  thf(sk_A_type, type, sk_A: $i).
% 0.95/1.23  thf(sk_B_type, type, sk_B: $i).
% 0.95/1.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.95/1.23  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.95/1.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.95/1.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.95/1.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.95/1.23  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.95/1.23  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.95/1.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.95/1.23  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.95/1.23  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.95/1.23  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.95/1.23  thf(sk_C_type, type, sk_C: $i).
% 0.95/1.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.95/1.23  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.95/1.23  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.95/1.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.95/1.23  thf(dt_u1_pre_topc, axiom,
% 0.95/1.23    (![A:$i]:
% 0.95/1.23     ( ( l1_pre_topc @ A ) =>
% 0.95/1.23       ( m1_subset_1 @
% 0.95/1.23         ( u1_pre_topc @ A ) @ 
% 0.95/1.23         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.95/1.23  thf('0', plain,
% 0.95/1.23      (![X7 : $i]:
% 0.95/1.23         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.95/1.23           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.95/1.23          | ~ (l1_pre_topc @ X7))),
% 0.95/1.23      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.95/1.23  thf(dt_g1_pre_topc, axiom,
% 0.95/1.23    (![A:$i,B:$i]:
% 0.95/1.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.95/1.23       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.95/1.23         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.95/1.23  thf('1', plain,
% 0.95/1.23      (![X5 : $i, X6 : $i]:
% 0.95/1.23         ((l1_pre_topc @ (g1_pre_topc @ X5 @ X6))
% 0.95/1.23          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.95/1.23      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.95/1.23  thf('2', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.23  thf('3', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.23  thf('4', plain,
% 0.95/1.23      (![X7 : $i]:
% 0.95/1.23         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.95/1.23           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.95/1.23          | ~ (l1_pre_topc @ X7))),
% 0.95/1.23      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.95/1.23  thf('5', plain,
% 0.95/1.23      (![X5 : $i, X6 : $i]:
% 0.95/1.23         ((v1_pre_topc @ (g1_pre_topc @ X5 @ X6))
% 0.95/1.23          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.95/1.23      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.95/1.23  thf('6', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | (v1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['4', '5'])).
% 0.95/1.23  thf(abstractness_v1_pre_topc, axiom,
% 0.95/1.23    (![A:$i]:
% 0.95/1.23     ( ( l1_pre_topc @ A ) =>
% 0.95/1.23       ( ( v1_pre_topc @ A ) =>
% 0.95/1.23         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.95/1.23  thf('7', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (v1_pre_topc @ X0)
% 0.95/1.23          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.95/1.23          | ~ (l1_pre_topc @ X0))),
% 0.95/1.23      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.95/1.23  thf('8', plain,
% 0.95/1.23      (![X7 : $i]:
% 0.95/1.23         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.95/1.23           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.95/1.23          | ~ (l1_pre_topc @ X7))),
% 0.95/1.23      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.95/1.23  thf(free_g1_pre_topc, axiom,
% 0.95/1.23    (![A:$i,B:$i]:
% 0.95/1.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.95/1.23       ( ![C:$i,D:$i]:
% 0.95/1.23         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.95/1.23           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.95/1.23  thf('9', plain,
% 0.95/1.23      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.95/1.23         (((g1_pre_topc @ X10 @ X11) != (g1_pre_topc @ X8 @ X9))
% 0.95/1.23          | ((X10) = (X8))
% 0.95/1.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.95/1.23      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.95/1.23  thf('10', plain,
% 0.95/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | ((u1_struct_0 @ X0) = (X1))
% 0.95/1.23          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.95/1.23              != (g1_pre_topc @ X1 @ X2)))),
% 0.95/1.23      inference('sup-', [status(thm)], ['8', '9'])).
% 0.95/1.23  thf('11', plain,
% 0.95/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.23         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.95/1.23          | ~ (l1_pre_topc @ X0)
% 0.95/1.23          | ~ (v1_pre_topc @ X0)
% 0.95/1.23          | ((u1_struct_0 @ X0) = (X2))
% 0.95/1.23          | ~ (l1_pre_topc @ X0))),
% 0.95/1.23      inference('sup-', [status(thm)], ['7', '10'])).
% 0.95/1.23  thf('12', plain,
% 0.95/1.23      (![X1 : $i, X2 : $i]:
% 0.95/1.23         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.95/1.23          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.95/1.23          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.95/1.23      inference('simplify', [status(thm)], ['11'])).
% 0.95/1.23  thf('13', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | ~ (l1_pre_topc @ 
% 0.95/1.23               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.95/1.23          | ((u1_struct_0 @ 
% 0.95/1.23              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.95/1.23              = (u1_struct_0 @ X0)))),
% 0.95/1.23      inference('sup-', [status(thm)], ['6', '12'])).
% 0.95/1.23  thf('14', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.23  thf('15', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (((u1_struct_0 @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.95/1.23            = (u1_struct_0 @ X0))
% 0.95/1.23          | ~ (l1_pre_topc @ X0))),
% 0.95/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 0.95/1.23  thf('16', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.23  thf('17', plain,
% 0.95/1.23      (![X0 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X0)
% 0.95/1.23          | (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.23  thf(t64_pre_topc, conjecture,
% 0.95/1.23    (![A:$i]:
% 0.95/1.23     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.95/1.23       ( ![B:$i]:
% 0.95/1.23         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.95/1.23           ( ![C:$i]:
% 0.95/1.23             ( ( ( v1_funct_1 @ C ) & 
% 0.95/1.23                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.95/1.23                 ( m1_subset_1 @
% 0.95/1.23                   C @ 
% 0.95/1.23                   ( k1_zfmisc_1 @
% 0.95/1.23                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.95/1.23               ( ![D:$i]:
% 0.95/1.23                 ( ( ( v1_funct_1 @ D ) & 
% 0.95/1.23                     ( v1_funct_2 @
% 0.95/1.23                       D @ 
% 0.95/1.23                       ( u1_struct_0 @
% 0.95/1.23                         ( g1_pre_topc @
% 0.95/1.23                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.95/1.23                       ( u1_struct_0 @
% 0.95/1.23                         ( g1_pre_topc @
% 0.95/1.23                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.95/1.23                     ( m1_subset_1 @
% 0.95/1.23                       D @ 
% 0.95/1.23                       ( k1_zfmisc_1 @
% 0.95/1.23                         ( k2_zfmisc_1 @
% 0.95/1.23                           ( u1_struct_0 @
% 0.95/1.23                             ( g1_pre_topc @
% 0.95/1.23                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.95/1.23                           ( u1_struct_0 @
% 0.95/1.23                             ( g1_pre_topc @
% 0.95/1.23                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.95/1.23                   ( ( ( C ) = ( D ) ) =>
% 0.95/1.23                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.95/1.23                       ( v5_pre_topc @
% 0.95/1.23                         D @ 
% 0.95/1.23                         ( g1_pre_topc @
% 0.95/1.23                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.95/1.23                         ( g1_pre_topc @
% 0.95/1.23                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.95/1.23  thf(zf_stmt_0, negated_conjecture,
% 0.95/1.23    (~( ![A:$i]:
% 0.95/1.23        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.95/1.23          ( ![B:$i]:
% 0.95/1.23            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.95/1.23              ( ![C:$i]:
% 0.95/1.23                ( ( ( v1_funct_1 @ C ) & 
% 0.95/1.23                    ( v1_funct_2 @
% 0.95/1.23                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.95/1.23                    ( m1_subset_1 @
% 0.95/1.23                      C @ 
% 0.95/1.23                      ( k1_zfmisc_1 @
% 0.95/1.23                        ( k2_zfmisc_1 @
% 0.95/1.23                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.95/1.23                  ( ![D:$i]:
% 0.95/1.23                    ( ( ( v1_funct_1 @ D ) & 
% 0.95/1.23                        ( v1_funct_2 @
% 0.95/1.23                          D @ 
% 0.95/1.23                          ( u1_struct_0 @
% 0.95/1.23                            ( g1_pre_topc @
% 0.95/1.23                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.95/1.23                          ( u1_struct_0 @
% 0.95/1.23                            ( g1_pre_topc @
% 0.95/1.23                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.95/1.23                        ( m1_subset_1 @
% 0.95/1.23                          D @ 
% 0.95/1.23                          ( k1_zfmisc_1 @
% 0.95/1.23                            ( k2_zfmisc_1 @
% 0.95/1.23                              ( u1_struct_0 @
% 0.95/1.23                                ( g1_pre_topc @
% 0.95/1.23                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.95/1.23                              ( u1_struct_0 @
% 0.95/1.23                                ( g1_pre_topc @
% 0.95/1.23                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.95/1.23                      ( ( ( C ) = ( D ) ) =>
% 0.95/1.23                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.95/1.23                          ( v5_pre_topc @
% 0.95/1.23                            D @ 
% 0.95/1.23                            ( g1_pre_topc @
% 0.95/1.23                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.95/1.23                            ( g1_pre_topc @
% 0.95/1.23                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.95/1.23    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 0.95/1.23  thf('18', plain,
% 0.95/1.23      ((m1_subset_1 @ sk_D_1 @ 
% 0.95/1.23        (k1_zfmisc_1 @ 
% 0.95/1.23         (k2_zfmisc_1 @ 
% 0.95/1.23          (u1_struct_0 @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23          (u1_struct_0 @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.95/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.23  thf('19', plain, (((sk_C) = (sk_D_1))),
% 0.95/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.23  thf('20', plain,
% 0.95/1.23      ((m1_subset_1 @ sk_C @ 
% 0.95/1.23        (k1_zfmisc_1 @ 
% 0.95/1.23         (k2_zfmisc_1 @ 
% 0.95/1.23          (u1_struct_0 @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23          (u1_struct_0 @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.95/1.23      inference('demod', [status(thm)], ['18', '19'])).
% 0.95/1.23  thf(d12_pre_topc, axiom,
% 0.95/1.23    (![A:$i]:
% 0.95/1.23     ( ( l1_pre_topc @ A ) =>
% 0.95/1.23       ( ![B:$i]:
% 0.95/1.23         ( ( l1_pre_topc @ B ) =>
% 0.95/1.23           ( ![C:$i]:
% 0.95/1.23             ( ( ( v1_funct_1 @ C ) & 
% 0.95/1.23                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.95/1.23                 ( m1_subset_1 @
% 0.95/1.23                   C @ 
% 0.95/1.23                   ( k1_zfmisc_1 @
% 0.95/1.23                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.95/1.23               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.95/1.23                 ( ![D:$i]:
% 0.95/1.23                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.95/1.23                     ( ( v4_pre_topc @ D @ B ) =>
% 0.95/1.23                       ( v4_pre_topc @
% 0.95/1.23                         ( k8_relset_1 @
% 0.95/1.23                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.95/1.23                         A ) ) ) ) ) ) ) ) ) ))).
% 0.95/1.23  thf('21', plain,
% 0.95/1.23      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.95/1.23         (~ (l1_pre_topc @ X1)
% 0.95/1.23          | (m1_subset_1 @ (sk_D @ X2 @ X1 @ X3) @ 
% 0.95/1.23             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.95/1.23          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.95/1.23          | ~ (m1_subset_1 @ X2 @ 
% 0.95/1.23               (k1_zfmisc_1 @ 
% 0.95/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.95/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.95/1.23          | ~ (v1_funct_1 @ X2)
% 0.95/1.23          | ~ (l1_pre_topc @ X3))),
% 0.95/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.95/1.23  thf('22', plain,
% 0.95/1.23      ((~ (l1_pre_topc @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.95/1.23        | ~ (v1_funct_1 @ sk_C)
% 0.95/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 0.95/1.23             (u1_struct_0 @ 
% 0.95/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23             (u1_struct_0 @ 
% 0.95/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.95/1.23        | (v5_pre_topc @ sk_C @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.95/1.23        | (m1_subset_1 @ 
% 0.95/1.23           (sk_D @ sk_C @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23           (k1_zfmisc_1 @ 
% 0.95/1.23            (u1_struct_0 @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.95/1.23        | ~ (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.95/1.23      inference('sup-', [status(thm)], ['20', '21'])).
% 0.95/1.23  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.95/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.23  thf('24', plain,
% 0.95/1.23      ((v1_funct_2 @ sk_D_1 @ 
% 0.95/1.23        (u1_struct_0 @ 
% 0.95/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23        (u1_struct_0 @ 
% 0.95/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.95/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.23  thf('25', plain, (((sk_C) = (sk_D_1))),
% 0.95/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.23  thf('26', plain,
% 0.95/1.23      ((v1_funct_2 @ sk_C @ 
% 0.95/1.23        (u1_struct_0 @ 
% 0.95/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23        (u1_struct_0 @ 
% 0.95/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.95/1.23      inference('demod', [status(thm)], ['24', '25'])).
% 0.95/1.23  thf('27', plain,
% 0.95/1.23      ((~ (l1_pre_topc @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.95/1.23        | (v5_pre_topc @ sk_C @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.95/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.95/1.23        | (m1_subset_1 @ 
% 0.95/1.23           (sk_D @ sk_C @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23           (k1_zfmisc_1 @ 
% 0.95/1.23            (u1_struct_0 @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.95/1.23        | ~ (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.95/1.23      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.95/1.23  thf('28', plain,
% 0.95/1.23      ((~ (l1_pre_topc @ sk_A)
% 0.95/1.23        | ~ (l1_pre_topc @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.95/1.23        | (m1_subset_1 @ 
% 0.95/1.23           (sk_D @ sk_C @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.95/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.95/1.23           (k1_zfmisc_1 @ 
% 0.95/1.23            (u1_struct_0 @ 
% 0.95/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.95/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['17', '27'])).
% 1.06/1.23  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('30', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (m1_subset_1 @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (k1_zfmisc_1 @ 
% 1.06/1.23            (u1_struct_0 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['28', '29'])).
% 1.06/1.23  thf('31', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (m1_subset_1 @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (k1_zfmisc_1 @ 
% 1.06/1.23            (u1_struct_0 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['16', '30'])).
% 1.06/1.23  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('33', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (m1_subset_1 @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (k1_zfmisc_1 @ 
% 1.06/1.23            (u1_struct_0 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 1.06/1.23      inference('demod', [status(thm)], ['31', '32'])).
% 1.06/1.23  thf('34', plain,
% 1.06/1.23      (((m1_subset_1 @ 
% 1.06/1.23         (sk_D @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup+', [status(thm)], ['15', '33'])).
% 1.06/1.23  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('36', plain,
% 1.06/1.23      (((m1_subset_1 @ 
% 1.06/1.23         (sk_D @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['34', '35'])).
% 1.06/1.23  thf('37', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('38', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('39', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 1.06/1.23      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.23  thf('40', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | (v4_pre_topc @ (sk_D @ X2 @ X1 @ X3) @ X1)
% 1.06/1.23          | (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('41', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['39', '40'])).
% 1.06/1.23  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('43', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.23  thf('44', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.06/1.23  thf('45', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['38', '44'])).
% 1.06/1.23  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('47', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['45', '46'])).
% 1.06/1.23  thf('48', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['37', '47'])).
% 1.06/1.23  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('50', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['48', '49'])).
% 1.06/1.23  thf('51', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf(t61_pre_topc, axiom,
% 1.06/1.23    (![A:$i]:
% 1.06/1.23     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.23       ( ![B:$i]:
% 1.06/1.23         ( ( ( v4_pre_topc @ B @ A ) & 
% 1.06/1.23             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 1.06/1.23           ( ( v4_pre_topc @
% 1.06/1.23               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.06/1.23             ( m1_subset_1 @
% 1.06/1.23               B @ 
% 1.06/1.23               ( k1_zfmisc_1 @
% 1.06/1.23                 ( u1_struct_0 @
% 1.06/1.23                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 1.06/1.23  thf('52', plain,
% 1.06/1.23      (![X12 : $i, X13 : $i]:
% 1.06/1.23         (~ (v4_pre_topc @ X12 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 1.06/1.23          | ~ (m1_subset_1 @ X12 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (u1_struct_0 @ 
% 1.06/1.23                 (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))))
% 1.06/1.23          | (v4_pre_topc @ X12 @ X13)
% 1.06/1.23          | ~ (l1_pre_topc @ X13)
% 1.06/1.23          | ~ (v2_pre_topc @ X13))),
% 1.06/1.23      inference('cnf', [status(esa)], [t61_pre_topc])).
% 1.06/1.23  thf('53', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.06/1.23          | ~ (l1_pre_topc @ X0)
% 1.06/1.23          | ~ (v2_pre_topc @ X0)
% 1.06/1.23          | ~ (l1_pre_topc @ X0)
% 1.06/1.23          | (v4_pre_topc @ X1 @ X0)
% 1.06/1.23          | ~ (v4_pre_topc @ X1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.23  thf('54', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         (~ (v4_pre_topc @ X1 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23          | (v4_pre_topc @ X1 @ X0)
% 1.06/1.23          | ~ (v2_pre_topc @ X0)
% 1.06/1.23          | ~ (l1_pre_topc @ X0)
% 1.06/1.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.06/1.23      inference('simplify', [status(thm)], ['53'])).
% 1.06/1.23  thf('55', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (m1_subset_1 @ 
% 1.06/1.23             (sk_D @ sk_C @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | ~ (v2_pre_topc @ sk_B)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['50', '54'])).
% 1.06/1.23  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('57', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('58', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (m1_subset_1 @ 
% 1.06/1.23             (sk_D @ sk_C @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.06/1.23  thf('59', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['36', '58'])).
% 1.06/1.23  thf('60', plain,
% 1.06/1.23      (((v4_pre_topc @ 
% 1.06/1.23         (sk_D @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('simplify', [status(thm)], ['59'])).
% 1.06/1.23  thf('61', plain,
% 1.06/1.23      (((m1_subset_1 @ 
% 1.06/1.23         (sk_D @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['34', '35'])).
% 1.06/1.23  thf('62', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('63', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('64', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 1.06/1.23         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 1.06/1.23      inference('split', [status(esa)], ['63'])).
% 1.06/1.23  thf('65', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('66', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 1.06/1.23      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.23  thf('67', plain,
% 1.06/1.23      (((m1_subset_1 @ sk_C @ 
% 1.06/1.23         (k1_zfmisc_1 @ 
% 1.06/1.23          (k2_zfmisc_1 @ 
% 1.06/1.23           (u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (u1_struct_0 @ sk_B))))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B))),
% 1.06/1.23      inference('sup+', [status(thm)], ['65', '66'])).
% 1.06/1.23  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('69', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['67', '68'])).
% 1.06/1.23  thf(t62_pre_topc, axiom,
% 1.06/1.23    (![A:$i]:
% 1.06/1.23     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.23       ( ![B:$i]:
% 1.06/1.23         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 1.06/1.23           ( ![C:$i]:
% 1.06/1.23             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.23                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.23                 ( m1_subset_1 @
% 1.06/1.23                   C @ 
% 1.06/1.23                   ( k1_zfmisc_1 @
% 1.06/1.23                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.23               ( ![D:$i]:
% 1.06/1.23                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.23                     ( v1_funct_2 @
% 1.06/1.23                       D @ 
% 1.06/1.23                       ( u1_struct_0 @
% 1.06/1.23                         ( g1_pre_topc @
% 1.06/1.23                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 1.06/1.23                       ( u1_struct_0 @ B ) ) & 
% 1.06/1.23                     ( m1_subset_1 @
% 1.06/1.23                       D @ 
% 1.06/1.23                       ( k1_zfmisc_1 @
% 1.06/1.23                         ( k2_zfmisc_1 @
% 1.06/1.23                           ( u1_struct_0 @
% 1.06/1.23                             ( g1_pre_topc @
% 1.06/1.23                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 1.06/1.23                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.23                   ( ( ( C ) = ( D ) ) =>
% 1.06/1.23                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 1.06/1.23                       ( v5_pre_topc @
% 1.06/1.23                         D @ 
% 1.06/1.23                         ( g1_pre_topc @
% 1.06/1.23                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 1.06/1.23                         B ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.23  thf('70', plain,
% 1.06/1.23      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.06/1.23         (~ (v2_pre_topc @ X15)
% 1.06/1.23          | ~ (l1_pre_topc @ X15)
% 1.06/1.23          | ~ (v1_funct_1 @ X16)
% 1.06/1.23          | ~ (v1_funct_2 @ X16 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23               (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (m1_subset_1 @ X16 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23                 (u1_struct_0 @ X15))))
% 1.06/1.23          | ~ (v5_pre_topc @ X18 @ X17 @ X15)
% 1.06/1.23          | (v5_pre_topc @ X16 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)) @ X15)
% 1.06/1.23          | ((X18) != (X16))
% 1.06/1.23          | ~ (m1_subset_1 @ X18 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 1.06/1.23          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (v1_funct_1 @ X18)
% 1.06/1.23          | ~ (l1_pre_topc @ X17)
% 1.06/1.23          | ~ (v2_pre_topc @ X17))),
% 1.06/1.23      inference('cnf', [status(esa)], [t62_pre_topc])).
% 1.06/1.23  thf('71', plain,
% 1.06/1.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.06/1.23         (~ (v2_pre_topc @ X17)
% 1.06/1.23          | ~ (l1_pre_topc @ X17)
% 1.06/1.23          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (m1_subset_1 @ X16 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 1.06/1.23          | (v5_pre_topc @ X16 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)) @ X15)
% 1.06/1.23          | ~ (v5_pre_topc @ X16 @ X17 @ X15)
% 1.06/1.23          | ~ (m1_subset_1 @ X16 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23                 (u1_struct_0 @ X15))))
% 1.06/1.23          | ~ (v1_funct_2 @ X16 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23               (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (v1_funct_1 @ X16)
% 1.06/1.23          | ~ (l1_pre_topc @ X15)
% 1.06/1.23          | ~ (v2_pre_topc @ X15))),
% 1.06/1.23      inference('simplify', [status(thm)], ['70'])).
% 1.06/1.23  thf('72', plain,
% 1.06/1.23      ((~ (v2_pre_topc @ sk_B)
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ sk_B))
% 1.06/1.23        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.23             (k1_zfmisc_1 @ 
% 1.06/1.23              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.23        | ~ (v2_pre_topc @ sk_A))),
% 1.06/1.23      inference('sup-', [status(thm)], ['69', '71'])).
% 1.06/1.23  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('76', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('77', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.23  thf('78', plain,
% 1.06/1.23      (((v1_funct_2 @ sk_C @ 
% 1.06/1.23         (u1_struct_0 @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (u1_struct_0 @ sk_B))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B))),
% 1.06/1.23      inference('sup+', [status(thm)], ['76', '77'])).
% 1.06/1.23  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('80', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.23  thf('81', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('82', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('85', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)],
% 1.06/1.23                ['72', '73', '74', '75', '80', '81', '82', '83', '84'])).
% 1.06/1.23  thf('86', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 1.06/1.23         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 1.06/1.23      inference('sup-', [status(thm)], ['64', '85'])).
% 1.06/1.23  thf('87', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['67', '68'])).
% 1.06/1.23  thf('88', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | ~ (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (v4_pre_topc @ X4 @ X1)
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ X4) @ 
% 1.06/1.23             X3)
% 1.06/1.23          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('89', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23          | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ sk_B))
% 1.06/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v4_pre_topc @ X0 @ sk_B)
% 1.06/1.23          | ~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               sk_B)
% 1.06/1.23          | ~ (l1_pre_topc @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['87', '88'])).
% 1.06/1.23  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('91', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.23  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('93', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v4_pre_topc @ X0 @ sk_B)
% 1.06/1.23          | ~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 1.06/1.23  thf('94', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (v4_pre_topc @ X0 @ sk_B)
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23           | ~ (l1_pre_topc @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 1.06/1.23      inference('sup-', [status(thm)], ['86', '93'])).
% 1.06/1.23  thf('95', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (l1_pre_topc @ sk_A)
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 1.06/1.23      inference('sup-', [status(thm)], ['62', '94'])).
% 1.06/1.23  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('97', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 1.06/1.23      inference('demod', [status(thm)], ['95', '96'])).
% 1.06/1.23  thf('98', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('99', plain, (((sk_C) = (sk_D_1))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('100', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['98', '99'])).
% 1.06/1.23  thf('101', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_C @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('split', [status(esa)], ['100'])).
% 1.06/1.23  thf('102', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('103', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (~
% 1.06/1.23             ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('split', [status(esa)], ['102'])).
% 1.06/1.23  thf('104', plain, (((sk_C) = (sk_D_1))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('105', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (~
% 1.06/1.23             ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['103', '104'])).
% 1.06/1.23  thf('106', plain,
% 1.06/1.23      (~
% 1.06/1.23       ((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 1.06/1.23       ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['101', '105'])).
% 1.06/1.23  thf('107', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('108', plain, (((sk_C) = (sk_D_1))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('109', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['107', '108'])).
% 1.06/1.23  thf('110', plain,
% 1.06/1.23      (~
% 1.06/1.23       ((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 1.06/1.23       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('split', [status(esa)], ['109'])).
% 1.06/1.23  thf('111', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('112', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('113', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('114', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('115', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['67', '68'])).
% 1.06/1.23  thf('116', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | (m1_subset_1 @ (sk_D @ X2 @ X1 @ X3) @ 
% 1.06/1.23             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.06/1.23          | (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('117', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ sk_B))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (m1_subset_1 @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['115', '116'])).
% 1.06/1.23  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('119', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.23  thf('120', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('121', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (m1_subset_1 @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 1.06/1.23  thf('122', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.23        | (m1_subset_1 @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['114', '121'])).
% 1.06/1.23  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('124', plain,
% 1.06/1.23      (((m1_subset_1 @ 
% 1.06/1.23         (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['122', '123'])).
% 1.06/1.23  thf('125', plain,
% 1.06/1.23      (![X13 : $i, X14 : $i]:
% 1.06/1.23         (~ (v4_pre_topc @ X14 @ X13)
% 1.06/1.23          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.06/1.23          | (v4_pre_topc @ X14 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 1.06/1.23          | ~ (l1_pre_topc @ X13)
% 1.06/1.23          | ~ (v2_pre_topc @ X13))),
% 1.06/1.23      inference('cnf', [status(esa)], [t61_pre_topc])).
% 1.06/1.23  thf('126', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | ~ (v2_pre_topc @ sk_B)
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (v4_pre_topc @ 
% 1.06/1.23             (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['124', '125'])).
% 1.06/1.23  thf('127', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('129', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (v4_pre_topc @ 
% 1.06/1.23             (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['126', '127', '128'])).
% 1.06/1.23  thf('130', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('131', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['67', '68'])).
% 1.06/1.23  thf('132', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | (v4_pre_topc @ (sk_D @ X2 @ X1 @ X3) @ X1)
% 1.06/1.23          | (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('133', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ sk_B))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           sk_B)
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['131', '132'])).
% 1.06/1.23  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('135', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.23  thf('136', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('137', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 1.06/1.23  thf('138', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['130', '137'])).
% 1.06/1.23  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('140', plain,
% 1.06/1.23      (((v4_pre_topc @ 
% 1.06/1.23         (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['138', '139'])).
% 1.06/1.23  thf('141', plain,
% 1.06/1.23      (((v4_pre_topc @ 
% 1.06/1.23         (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('clc', [status(thm)], ['129', '140'])).
% 1.06/1.23  thf('142', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('143', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('144', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X0)
% 1.06/1.23          | (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.23  thf('145', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('split', [status(esa)], ['63'])).
% 1.06/1.23  thf('146', plain, (((sk_C) = (sk_D_1))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('147', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['145', '146'])).
% 1.06/1.23  thf('148', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 1.06/1.23      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.23  thf('149', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | ~ (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (v4_pre_topc @ X4 @ X1)
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ X4) @ 
% 1.06/1.23             X3)
% 1.06/1.23          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('150', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23          | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (u1_struct_0 @ 
% 1.06/1.23                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23              sk_C @ X0) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23          | ~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23          | ~ (l1_pre_topc @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['148', '149'])).
% 1.06/1.23  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('152', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.23  thf('153', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (u1_struct_0 @ 
% 1.06/1.23                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23              sk_C @ X0) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23          | ~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23          | ~ (l1_pre_topc @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['150', '151', '152'])).
% 1.06/1.23  thf('154', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (l1_pre_topc @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23                (k1_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23           | ~ (l1_pre_topc @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['147', '153'])).
% 1.06/1.23  thf('155', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (l1_pre_topc @ sk_B)
% 1.06/1.23           | ~ (l1_pre_topc @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23                (k1_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['144', '154'])).
% 1.06/1.23  thf('156', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('157', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (l1_pre_topc @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23                (k1_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['155', '156'])).
% 1.06/1.23  thf('158', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (l1_pre_topc @ sk_A)
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23                (k1_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['143', '157'])).
% 1.06/1.23  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('160', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (v4_pre_topc @ X0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.23                (k1_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['158', '159'])).
% 1.06/1.23  thf('161', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23           | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['142', '160'])).
% 1.06/1.23  thf('162', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('163', plain,
% 1.06/1.23      ((![X0 : $i]:
% 1.06/1.23          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23           | (v4_pre_topc @ 
% 1.06/1.23              (k8_relset_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23               sk_C @ X0) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23           | ~ (v4_pre_topc @ X0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['161', '162'])).
% 1.06/1.23  thf('164', plain,
% 1.06/1.23      ((((v5_pre_topc @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23         | (v4_pre_topc @ 
% 1.06/1.23            (k8_relset_1 @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23             sk_C @ 
% 1.06/1.23             (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | ~ (m1_subset_1 @ 
% 1.06/1.23              (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['141', '163'])).
% 1.06/1.23  thf('165', plain,
% 1.06/1.23      (((m1_subset_1 @ 
% 1.06/1.23         (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['122', '123'])).
% 1.06/1.23  thf('166', plain,
% 1.06/1.23      ((((v4_pre_topc @ 
% 1.06/1.23          (k8_relset_1 @ 
% 1.06/1.23           (u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23           (u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23           sk_C @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('clc', [status(thm)], ['164', '165'])).
% 1.06/1.23  thf('167', plain,
% 1.06/1.23      ((((v4_pre_topc @ 
% 1.06/1.23          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.23           (u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23           sk_C @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup+', [status(thm)], ['113', '166'])).
% 1.06/1.23  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('169', plain,
% 1.06/1.23      ((((v4_pre_topc @ 
% 1.06/1.23          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.23           (u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.06/1.23           sk_C @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['167', '168'])).
% 1.06/1.23  thf('170', plain,
% 1.06/1.23      ((((v4_pre_topc @ 
% 1.06/1.23          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup+', [status(thm)], ['112', '169'])).
% 1.06/1.23  thf('171', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('172', plain,
% 1.06/1.23      ((((v4_pre_topc @ 
% 1.06/1.23          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.06/1.23           (sk_D @ sk_C @ sk_B @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['170', '171'])).
% 1.06/1.23  thf('173', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('174', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | ~ (v4_pre_topc @ 
% 1.06/1.23               (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ 
% 1.06/1.23                (sk_D @ X2 @ X1 @ X3)) @ 
% 1.06/1.23               X3)
% 1.06/1.23          | (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('175', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.23         (~ (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 1.06/1.23              (sk_D @ X2 @ X1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23          | ~ (l1_pre_topc @ X0)
% 1.06/1.23          | ~ (l1_pre_topc @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.06/1.23               (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.06/1.23                 (u1_struct_0 @ X1))))
% 1.06/1.23          | (v5_pre_topc @ X2 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 1.06/1.23          | ~ (l1_pre_topc @ X1))),
% 1.06/1.23      inference('sup-', [status(thm)], ['173', '174'])).
% 1.06/1.23  thf('176', plain,
% 1.06/1.23      ((((v5_pre_topc @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.23              (k1_zfmisc_1 @ 
% 1.06/1.23               (k2_zfmisc_1 @ 
% 1.06/1.23                (u1_struct_0 @ 
% 1.06/1.23                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23                (u1_struct_0 @ sk_B))))
% 1.06/1.23         | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (u1_struct_0 @ sk_B))
% 1.06/1.23         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23         | ~ (l1_pre_topc @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | ~ (l1_pre_topc @ sk_A)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['172', '175'])).
% 1.06/1.23  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('178', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['67', '68'])).
% 1.06/1.23  thf('179', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.23  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('182', plain,
% 1.06/1.23      ((((v5_pre_topc @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23         | ~ (l1_pre_topc @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)],
% 1.06/1.23                ['176', '177', '178', '179', '180', '181'])).
% 1.06/1.23  thf('183', plain,
% 1.06/1.23      (((~ (l1_pre_topc @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('simplify', [status(thm)], ['182'])).
% 1.06/1.23  thf('184', plain,
% 1.06/1.23      (((~ (l1_pre_topc @ sk_A)
% 1.06/1.23         | (v5_pre_topc @ sk_C @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['111', '183'])).
% 1.06/1.23  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('186', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['184', '185'])).
% 1.06/1.23  thf('187', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['67', '68'])).
% 1.06/1.23  thf('188', plain,
% 1.06/1.23      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.06/1.23         (~ (v2_pre_topc @ X15)
% 1.06/1.23          | ~ (l1_pre_topc @ X15)
% 1.06/1.23          | ~ (v1_funct_1 @ X16)
% 1.06/1.23          | ~ (v1_funct_2 @ X16 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23               (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (m1_subset_1 @ X16 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23                 (u1_struct_0 @ X15))))
% 1.06/1.23          | ~ (v5_pre_topc @ X16 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)) @ X15)
% 1.06/1.23          | (v5_pre_topc @ X18 @ X17 @ X15)
% 1.06/1.23          | ((X18) != (X16))
% 1.06/1.23          | ~ (m1_subset_1 @ X18 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 1.06/1.23          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (v1_funct_1 @ X18)
% 1.06/1.23          | ~ (l1_pre_topc @ X17)
% 1.06/1.23          | ~ (v2_pre_topc @ X17))),
% 1.06/1.23      inference('cnf', [status(esa)], [t62_pre_topc])).
% 1.06/1.23  thf('189', plain,
% 1.06/1.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.06/1.23         (~ (v2_pre_topc @ X17)
% 1.06/1.23          | ~ (l1_pre_topc @ X17)
% 1.06/1.23          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (m1_subset_1 @ X16 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 1.06/1.23          | (v5_pre_topc @ X16 @ X17 @ X15)
% 1.06/1.23          | ~ (v5_pre_topc @ X16 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)) @ X15)
% 1.06/1.23          | ~ (m1_subset_1 @ X16 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23                 (u1_struct_0 @ X15))))
% 1.06/1.23          | ~ (v1_funct_2 @ X16 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17))) @ 
% 1.06/1.23               (u1_struct_0 @ X15))
% 1.06/1.23          | ~ (v1_funct_1 @ X16)
% 1.06/1.23          | ~ (l1_pre_topc @ X15)
% 1.06/1.23          | ~ (v2_pre_topc @ X15))),
% 1.06/1.23      inference('simplify', [status(thm)], ['188'])).
% 1.06/1.23  thf('190', plain,
% 1.06/1.23      ((~ (v2_pre_topc @ sk_B)
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ sk_B))
% 1.06/1.23        | ~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 1.06/1.23        | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.23             (k1_zfmisc_1 @ 
% 1.06/1.23              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.23        | ~ (v2_pre_topc @ sk_A))),
% 1.06/1.23      inference('sup-', [status(thm)], ['187', '189'])).
% 1.06/1.23  thf('191', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('192', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('194', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.23  thf('195', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('196', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('199', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 1.06/1.23        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)],
% 1.06/1.23                ['190', '191', '192', '193', '194', '195', '196', '197', '198'])).
% 1.06/1.23  thf('200', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['186', '199'])).
% 1.06/1.23  thf('201', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 1.06/1.23         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 1.06/1.23      inference('split', [status(esa)], ['102'])).
% 1.06/1.23  thf('202', plain,
% 1.06/1.23      (~
% 1.06/1.23       ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 1.06/1.23       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['200', '201'])).
% 1.06/1.23  thf('203', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 1.06/1.23       ((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('split', [status(esa)], ['100'])).
% 1.06/1.23  thf('204', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 1.06/1.23      inference('sat_resolution*', [status(thm)], ['106', '110', '202', '203'])).
% 1.06/1.23  thf('205', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.06/1.23          | (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ 
% 1.06/1.23              (u1_struct_0 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23          | ~ (v4_pre_topc @ X0 @ sk_B))),
% 1.06/1.23      inference('simpl_trail', [status(thm)], ['97', '204'])).
% 1.06/1.23  thf('206', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (v4_pre_topc @ 
% 1.06/1.23             (sk_D @ sk_C @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             sk_B)
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (k8_relset_1 @ 
% 1.06/1.23            (u1_struct_0 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23            (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.06/1.23            (sk_D @ sk_C @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['61', '205'])).
% 1.06/1.23  thf('207', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (~
% 1.06/1.23             ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['103', '104'])).
% 1.06/1.23  thf('208', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('demod', [status(thm)], ['145', '146'])).
% 1.06/1.23  thf('209', plain,
% 1.06/1.23      ((~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23         <= (~
% 1.06/1.23             ((v5_pre_topc @ sk_C @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 1.06/1.23      inference('split', [status(esa)], ['109'])).
% 1.06/1.23  thf('210', plain,
% 1.06/1.23      (~
% 1.06/1.23       ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 1.06/1.23       ((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['208', '209'])).
% 1.06/1.23  thf('211', plain,
% 1.06/1.23      (~
% 1.06/1.23       ((v5_pre_topc @ sk_D_1 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sat_resolution*', [status(thm)], ['106', '110', '202', '210'])).
% 1.06/1.23  thf('212', plain,
% 1.06/1.23      (~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.06/1.23      inference('simpl_trail', [status(thm)], ['207', '211'])).
% 1.06/1.23  thf('213', plain,
% 1.06/1.23      (((v4_pre_topc @ 
% 1.06/1.23         (k8_relset_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.06/1.23          (sk_D @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | ~ (v4_pre_topc @ 
% 1.06/1.23             (sk_D @ sk_C @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             sk_B))),
% 1.06/1.23      inference('clc', [status(thm)], ['206', '212'])).
% 1.06/1.23  thf('214', plain,
% 1.06/1.23      (((v5_pre_topc @ sk_C @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v4_pre_topc @ 
% 1.06/1.23           (k8_relset_1 @ 
% 1.06/1.23            (u1_struct_0 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23            (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.06/1.23            (sk_D @ sk_C @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['60', '213'])).
% 1.06/1.23  thf('215', plain,
% 1.06/1.23      (~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.06/1.23      inference('simpl_trail', [status(thm)], ['207', '211'])).
% 1.06/1.23  thf('216', plain,
% 1.06/1.23      ((v4_pre_topc @ 
% 1.06/1.23        (k8_relset_1 @ 
% 1.06/1.23         (u1_struct_0 @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23         (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.06/1.23         (sk_D @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 1.06/1.23        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.06/1.23      inference('clc', [status(thm)], ['214', '215'])).
% 1.06/1.23  thf('217', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         (((u1_struct_0 @ 
% 1.06/1.23            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23            = (u1_struct_0 @ X0))
% 1.06/1.23          | ~ (l1_pre_topc @ X0))),
% 1.06/1.23      inference('clc', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('218', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.23         (~ (l1_pre_topc @ X1)
% 1.06/1.23          | ~ (v4_pre_topc @ 
% 1.06/1.23               (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ 
% 1.06/1.23                (sk_D @ X2 @ X1 @ X3)) @ 
% 1.06/1.23               X3)
% 1.06/1.23          | (v5_pre_topc @ X2 @ X3 @ X1)
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (l1_pre_topc @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [d12_pre_topc])).
% 1.06/1.23  thf('219', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.23         (~ (v4_pre_topc @ 
% 1.06/1.23             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2 @ 
% 1.06/1.23              (sk_D @ X2 @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)) @ 
% 1.06/1.23             X1)
% 1.06/1.23          | ~ (l1_pre_topc @ X0)
% 1.06/1.23          | ~ (l1_pre_topc @ X1)
% 1.06/1.23          | ~ (v1_funct_1 @ X2)
% 1.06/1.23          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 1.06/1.23          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.23               (k1_zfmisc_1 @ 
% 1.06/1.23                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 1.06/1.23                 (u1_struct_0 @ 
% 1.06/1.23                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 1.06/1.23          | (v5_pre_topc @ X2 @ X1 @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.06/1.23          | ~ (l1_pre_topc @ 
% 1.06/1.23               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['217', '218'])).
% 1.06/1.23  thf('220', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.23             (k1_zfmisc_1 @ 
% 1.06/1.23              (k2_zfmisc_1 @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23               (u1_struct_0 @ 
% 1.06/1.23                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 1.06/1.23        | ~ (v1_funct_2 @ sk_C @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23             (u1_struct_0 @ 
% 1.06/1.23              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 1.06/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | ~ (l1_pre_topc @ sk_B))),
% 1.06/1.23      inference('sup-', [status(thm)], ['216', '219'])).
% 1.06/1.23  thf('221', plain,
% 1.06/1.23      ((m1_subset_1 @ sk_C @ 
% 1.06/1.23        (k1_zfmisc_1 @ 
% 1.06/1.23         (k2_zfmisc_1 @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23          (u1_struct_0 @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 1.06/1.23      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.23  thf('222', plain,
% 1.06/1.23      ((v1_funct_2 @ sk_C @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 1.06/1.23        (u1_struct_0 @ 
% 1.06/1.23         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.23  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('224', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('225', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | (v5_pre_topc @ sk_C @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 1.06/1.23      inference('demod', [status(thm)], ['220', '221', '222', '223', '224'])).
% 1.06/1.23  thf('226', plain,
% 1.06/1.23      (~ (v5_pre_topc @ sk_C @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.06/1.23      inference('simpl_trail', [status(thm)], ['207', '211'])).
% 1.06/1.23  thf('227', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ 
% 1.06/1.23           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('clc', [status(thm)], ['225', '226'])).
% 1.06/1.23  thf('228', plain,
% 1.06/1.23      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.23        | ~ (l1_pre_topc @ 
% 1.06/1.23             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['3', '227'])).
% 1.06/1.23  thf('229', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('230', plain,
% 1.06/1.23      (~ (l1_pre_topc @ 
% 1.06/1.23          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.06/1.23      inference('demod', [status(thm)], ['228', '229'])).
% 1.06/1.23  thf('231', plain, (~ (l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('sup-', [status(thm)], ['2', '230'])).
% 1.06/1.23  thf('232', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf('233', plain, ($false), inference('demod', [status(thm)], ['231', '232'])).
% 1.06/1.23  
% 1.06/1.23  % SZS output end Refutation
% 1.06/1.23  
% 1.06/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
