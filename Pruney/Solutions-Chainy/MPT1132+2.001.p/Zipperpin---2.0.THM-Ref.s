%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.buYLdAWhvu

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:27 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  197 (1510 expanded)
%              Number of leaves         :   26 ( 441 expanded)
%              Depth                    :   31
%              Number of atoms          : 2721 (48485 expanded)
%              Number of equality atoms :   26 ( 787 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_pre_topc @ X10 @ X11 )
       != ( g1_pre_topc @ X8 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

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

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('32',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('46',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('61',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X3 ) @ X1 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

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
    inference(demod,[status(thm)],['16','17'])).

thf('81',plain,(
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
    inference(demod,[status(thm)],['23','24'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ X0 ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','93'])).

thf('95',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('96',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X3 ) ) @ X3 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('101',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106'])).

thf('108',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('110',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('112',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('113',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['46','50','110','113'])).

thf('115',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['40','114'])).

thf('116',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['36','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['14','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['76'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
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

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
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

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('131',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['46','50','110','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['129','131'])).

thf('133',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['119','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('136',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X3 ) @ X1 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('141',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['36','115'])).

thf('146',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('147',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['144','150'])).

thf('152',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['40','114'])).

thf('153',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['133','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('156',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X3 ) ) @ X3 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 @ ( sk_D @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( v5_pre_topc @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('160',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162','163'])).

thf('165',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['40','114'])).

thf('166',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['2','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['167','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.buYLdAWhvu
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 563 iterations in 0.675s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.13  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.13  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.90/1.13  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.90/1.13  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.13  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.90/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.13  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.90/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(dt_u1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( m1_subset_1 @
% 0.90/1.13         ( u1_pre_topc @ A ) @ 
% 0.90/1.13         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.13  thf('0', plain,
% 0.90/1.13      (![X7 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.90/1.13          | ~ (l1_pre_topc @ X7))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.13  thf(dt_g1_pre_topc, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.13       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.90/1.13         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (![X5 : $i, X6 : $i]:
% 0.90/1.13         ((l1_pre_topc @ (g1_pre_topc @ X5 @ X6))
% 0.90/1.13          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (![X7 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.90/1.13          | ~ (l1_pre_topc @ X7))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X5 : $i, X6 : $i]:
% 0.90/1.13         ((v1_pre_topc @ (g1_pre_topc @ X5 @ X6))
% 0.90/1.13          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (v1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.13  thf(abstractness_v1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ( v1_pre_topc @ A ) =>
% 0.90/1.13         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_pre_topc @ X0)
% 0.90/1.13          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (![X7 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.90/1.13          | ~ (l1_pre_topc @ X7))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.13  thf(free_g1_pre_topc, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.13       ( ![C:$i,D:$i]:
% 0.90/1.13         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.90/1.13           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.90/1.13  thf('8', plain,
% 0.90/1.13      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.13         (((g1_pre_topc @ X10 @ X11) != (g1_pre_topc @ X8 @ X9))
% 0.90/1.13          | ((X10) = (X8))
% 0.90/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.90/1.13      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | ((u1_struct_0 @ X0) = (X1))
% 0.90/1.13          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.90/1.13              != (g1_pre_topc @ X1 @ X2)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.90/1.13          | ~ (l1_pre_topc @ X0)
% 0.90/1.13          | ~ (v1_pre_topc @ X0)
% 0.90/1.13          | ((u1_struct_0 @ X0) = (X2))
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['6', '9'])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (![X1 : $i, X2 : $i]:
% 0.90/1.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.90/1.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.90/1.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ 
% 0.90/1.13               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13          | ((u1_struct_0 @ 
% 0.90/1.13              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13              = (u1_struct_0 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '11'])).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((u1_struct_0 @ 
% 0.90/1.13            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13            = (u1_struct_0 @ X0))
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('clc', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_pre_topc @ X0)
% 0.90/1.13          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.90/1.13  thf(t63_pre_topc, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                 ( m1_subset_1 @
% 0.90/1.14                   C @ 
% 0.90/1.14                   ( k1_zfmisc_1 @
% 0.90/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14               ( ![D:$i]:
% 0.90/1.14                 ( ( ( v1_funct_1 @ D ) & 
% 0.90/1.14                     ( v1_funct_2 @
% 0.90/1.14                       D @ ( u1_struct_0 @ A ) @ 
% 0.90/1.14                       ( u1_struct_0 @
% 0.90/1.14                         ( g1_pre_topc @
% 0.90/1.14                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.90/1.14                     ( m1_subset_1 @
% 0.90/1.14                       D @ 
% 0.90/1.14                       ( k1_zfmisc_1 @
% 0.90/1.14                         ( k2_zfmisc_1 @
% 0.90/1.14                           ( u1_struct_0 @ A ) @ 
% 0.90/1.14                           ( u1_struct_0 @
% 0.90/1.14                             ( g1_pre_topc @
% 0.90/1.14                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.90/1.14                   ( ( ( C ) = ( D ) ) =>
% 0.90/1.14                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.90/1.14                       ( v5_pre_topc @
% 0.90/1.14                         D @ A @ 
% 0.90/1.14                         ( g1_pre_topc @
% 0.90/1.14                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i]:
% 0.90/1.14        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14          ( ![B:$i]:
% 0.90/1.14            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.90/1.14              ( ![C:$i]:
% 0.90/1.14                ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                    ( v1_funct_2 @
% 0.90/1.14                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                    ( m1_subset_1 @
% 0.90/1.14                      C @ 
% 0.90/1.14                      ( k1_zfmisc_1 @
% 0.90/1.14                        ( k2_zfmisc_1 @
% 0.90/1.14                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14                  ( ![D:$i]:
% 0.90/1.14                    ( ( ( v1_funct_1 @ D ) & 
% 0.90/1.14                        ( v1_funct_2 @
% 0.90/1.14                          D @ ( u1_struct_0 @ A ) @ 
% 0.90/1.14                          ( u1_struct_0 @
% 0.90/1.14                            ( g1_pre_topc @
% 0.90/1.14                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.90/1.14                        ( m1_subset_1 @
% 0.90/1.14                          D @ 
% 0.90/1.14                          ( k1_zfmisc_1 @
% 0.90/1.14                            ( k2_zfmisc_1 @
% 0.90/1.14                              ( u1_struct_0 @ A ) @ 
% 0.90/1.14                              ( u1_struct_0 @
% 0.90/1.14                                ( g1_pre_topc @
% 0.90/1.14                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.90/1.14                      ( ( ( C ) = ( D ) ) =>
% 0.90/1.14                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.90/1.14                          ( v5_pre_topc @
% 0.90/1.14                            D @ A @ 
% 0.90/1.14                            ( g1_pre_topc @
% 0.90/1.14                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t63_pre_topc])).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D_1 @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (u1_struct_0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('17', plain, (((sk_C) = (sk_D_1))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (u1_struct_0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.14      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.14  thf(d12_pre_topc, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_pre_topc @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( l1_pre_topc @ B ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                 ( m1_subset_1 @
% 0.90/1.14                   C @ 
% 0.90/1.14                   ( k1_zfmisc_1 @
% 0.90/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.90/1.14                 ( ![D:$i]:
% 0.90/1.14                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.90/1.14                     ( ( v4_pre_topc @ D @ B ) =>
% 0.90/1.14                       ( v4_pre_topc @
% 0.90/1.14                         ( k8_relset_1 @
% 0.90/1.14                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.90/1.14                         A ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | (m1_subset_1 @ (sk_D @ X2 @ X1 @ X3) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.90/1.14          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14             (u1_struct_0 @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | ~ (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['18', '19'])).
% 0.90/1.14  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14        (u1_struct_0 @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('24', plain, (((sk_C) = (sk_D_1))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14        (u1_struct_0 @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | ~ (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14        | ~ (v1_pre_topc @ sk_B)
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['15', '26'])).
% 0.90/1.14  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      ((~ (v1_pre_topc @ sk_B)
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X0)
% 0.90/1.14          | (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | ~ (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.14  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      (((m1_subset_1 @ 
% 0.90/1.14         (sk_D @ sk_C @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14         (k1_zfmisc_1 @ 
% 0.90/1.14          (u1_struct_0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['33', '34'])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ 
% 0.90/1.14            (u1_struct_0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.14      inference('clc', [status(thm)], ['30', '35'])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (~
% 0.90/1.14             ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('split', [status(esa)], ['37'])).
% 0.90/1.14  thf('39', plain, (((sk_C) = (sk_D_1))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('40', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (~
% 0.90/1.14             ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '39'])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('42', plain, (((sk_C) = (sk_D_1))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['41', '42'])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('split', [status(esa)], ['43'])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (~
% 0.90/1.14             ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '39'])).
% 0.90/1.14  thf('46', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.90/1.14       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('48', plain, (((sk_C) = (sk_D_1))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['47', '48'])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.90/1.14       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('split', [status(esa)], ['49'])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((u1_struct_0 @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14            = (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (l1_pre_topc @ X0))),
% 0.90/1.14      inference('clc', [status(thm)], ['12', '13'])).
% 0.90/1.14  thf('52', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | (m1_subset_1 @ (sk_D @ X2 @ X1 @ X3) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.90/1.14          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['52', '53'])).
% 0.90/1.14  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.90/1.14  thf(t61_pre_topc, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.90/1.14           ( ( v4_pre_topc @
% 0.90/1.14               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.90/1.14             ( m1_subset_1 @
% 0.90/1.14               B @ 
% 0.90/1.14               ( k1_zfmisc_1 @
% 0.90/1.14                 ( u1_struct_0 @
% 0.90/1.14                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      (![X13 : $i, X14 : $i]:
% 0.90/1.14         (~ (v4_pre_topc @ X14 @ X13)
% 0.90/1.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.90/1.14          | (v4_pre_topc @ X14 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.90/1.14          | ~ (l1_pre_topc @ X13)
% 0.90/1.14          | ~ (v2_pre_topc @ X13))),
% 0.90/1.14      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.14  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('64', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('66', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | (v4_pre_topc @ (sk_D @ X2 @ X1 @ X3) @ X1)
% 0.90/1.14          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('67', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.14  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('70', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      (((v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('clc', [status(thm)], ['64', '72'])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((u1_struct_0 @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14            = (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (l1_pre_topc @ X0))),
% 0.90/1.14      inference('clc', [status(thm)], ['12', '13'])).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X0)
% 0.90/1.14          | (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('split', [status(esa)], ['76'])).
% 0.90/1.14  thf('78', plain, (((sk_C) = (sk_D_1))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '78'])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (u1_struct_0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.14      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (v4_pre_topc @ X4 @ X1)
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ X4) @ 
% 0.90/1.14             X3)
% 0.90/1.14          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ sk_A)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (u1_struct_0 @ 
% 0.90/1.14                 (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14              sk_C @ X0) @ 
% 0.90/1.14             sk_A)
% 0.90/1.14          | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14          | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14          | ~ (l1_pre_topc @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['80', '81'])).
% 0.90/1.14  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('85', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14        (u1_struct_0 @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.14  thf('86', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X0 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14              sk_C @ X0) @ 
% 0.90/1.14             sk_A)
% 0.90/1.14          | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14          | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14          | ~ (l1_pre_topc @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      ((![X0 : $i]:
% 0.90/1.14          (~ (l1_pre_topc @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14           | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14           | (v4_pre_topc @ 
% 0.90/1.14              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14               sk_C @ X0) @ 
% 0.90/1.14              sk_A)
% 0.90/1.14           | ~ (m1_subset_1 @ X0 @ 
% 0.90/1.14                (k1_zfmisc_1 @ 
% 0.90/1.14                 (u1_struct_0 @ 
% 0.90/1.14                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['79', '86'])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      ((![X0 : $i]:
% 0.90/1.14          (~ (l1_pre_topc @ sk_B)
% 0.90/1.14           | ~ (m1_subset_1 @ X0 @ 
% 0.90/1.14                (k1_zfmisc_1 @ 
% 0.90/1.14                 (u1_struct_0 @ 
% 0.90/1.14                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14           | (v4_pre_topc @ 
% 0.90/1.14              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14               sk_C @ X0) @ 
% 0.90/1.14              sk_A)
% 0.90/1.14           | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['75', '87'])).
% 0.90/1.14  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('90', plain,
% 0.90/1.14      ((![X0 : $i]:
% 0.90/1.14          (~ (m1_subset_1 @ X0 @ 
% 0.90/1.14              (k1_zfmisc_1 @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14           | (v4_pre_topc @ 
% 0.90/1.14              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14               sk_C @ X0) @ 
% 0.90/1.14              sk_A)
% 0.90/1.14           | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['88', '89'])).
% 0.90/1.14  thf('91', plain,
% 0.90/1.14      ((![X0 : $i]:
% 0.90/1.14          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.14           | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14           | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14           | (v4_pre_topc @ 
% 0.90/1.14              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14               sk_C @ X0) @ 
% 0.90/1.14              sk_A)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['74', '90'])).
% 0.90/1.14  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('93', plain,
% 0.90/1.14      ((![X0 : $i]:
% 0.90/1.14          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.14           | ~ (v4_pre_topc @ X0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14           | (v4_pre_topc @ 
% 0.90/1.14              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14               sk_C @ X0) @ 
% 0.90/1.14              sk_A)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['91', '92'])).
% 0.90/1.14  thf('94', plain,
% 0.90/1.14      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14         | (v4_pre_topc @ 
% 0.90/1.14            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14             (u1_struct_0 @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.90/1.14            sk_A)
% 0.90/1.14         | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14              (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['73', '93'])).
% 0.90/1.14  thf('95', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.90/1.14  thf('96', plain,
% 0.90/1.14      ((((v4_pre_topc @ 
% 0.90/1.14          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14           (u1_struct_0 @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.90/1.14           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.90/1.14          sk_A)
% 0.90/1.14         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('clc', [status(thm)], ['94', '95'])).
% 0.90/1.14  thf('97', plain,
% 0.90/1.14      ((((v4_pre_topc @ 
% 0.90/1.14          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.90/1.14           (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.90/1.14          sk_A)
% 0.90/1.14         | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('sup+', [status(thm)], ['51', '96'])).
% 0.90/1.14  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('99', plain,
% 0.90/1.14      ((((v4_pre_topc @ 
% 0.90/1.14          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.90/1.14           (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.90/1.14          sk_A)
% 0.90/1.14         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['97', '98'])).
% 0.90/1.14  thf('100', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v4_pre_topc @ 
% 0.90/1.14               (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ 
% 0.90/1.14                (sk_D @ X2 @ X1 @ X3)) @ 
% 0.90/1.14               X3)
% 0.90/1.14          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('101', plain,
% 0.90/1.14      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14         | ~ (l1_pre_topc @ sk_A)
% 0.90/1.14         | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.90/1.14         | ~ (m1_subset_1 @ sk_C @ 
% 0.90/1.14              (k1_zfmisc_1 @ 
% 0.90/1.14               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.90/1.14         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14         | ~ (l1_pre_topc @ sk_B)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['99', '100'])).
% 0.90/1.14  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('104', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('105', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('107', plain,
% 0.90/1.14      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['101', '102', '103', '104', '105', '106'])).
% 0.90/1.14  thf('108', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('simplify', [status(thm)], ['107'])).
% 0.90/1.14  thf('109', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.90/1.14         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.90/1.14      inference('split', [status(esa)], ['37'])).
% 0.90/1.14  thf('110', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.90/1.14       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['108', '109'])).
% 0.90/1.14  thf('111', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '78'])).
% 0.90/1.14  thf('112', plain,
% 0.90/1.14      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14         <= (~
% 0.90/1.14             ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('split', [status(esa)], ['49'])).
% 0.90/1.14  thf('113', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.90/1.14       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['111', '112'])).
% 0.90/1.14  thf('114', plain,
% 0.90/1.14      (~
% 0.90/1.14       ((v5_pre_topc @ sk_D_1 @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['46', '50', '110', '113'])).
% 0.90/1.14  thf('115', plain,
% 0.90/1.14      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['40', '114'])).
% 0.90/1.14  thf('116', plain,
% 0.90/1.14      ((m1_subset_1 @ 
% 0.90/1.14        (sk_D @ sk_C @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (u1_struct_0 @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('clc', [status(thm)], ['36', '115'])).
% 0.90/1.14  thf('117', plain,
% 0.90/1.14      (((m1_subset_1 @ 
% 0.90/1.14         (sk_D @ sk_C @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['14', '116'])).
% 0.90/1.14  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('119', plain,
% 0.90/1.14      ((m1_subset_1 @ 
% 0.90/1.14        (sk_D @ sk_C @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.14      inference('demod', [status(thm)], ['117', '118'])).
% 0.90/1.14  thf('120', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.90/1.14         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.90/1.14      inference('split', [status(esa)], ['76'])).
% 0.90/1.14  thf('121', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('122', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (v4_pre_topc @ X4 @ X1)
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ X4) @ 
% 0.90/1.14             X3)
% 0.90/1.14          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('123', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ sk_A)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14              sk_C @ X0) @ 
% 0.90/1.14             sk_A)
% 0.90/1.14          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.90/1.14          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['121', '122'])).
% 0.90/1.14  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('126', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('127', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('128', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14              sk_C @ X0) @ 
% 0.90/1.14             sk_A)
% 0.90/1.14          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.90/1.14          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.90/1.14  thf('129', plain,
% 0.90/1.14      ((![X0 : $i]:
% 0.90/1.14          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.90/1.14           | (v4_pre_topc @ 
% 0.90/1.14              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_C @ X0) @ 
% 0.90/1.14              sk_A)
% 0.90/1.14           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.90/1.14         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['120', '128'])).
% 0.90/1.14  thf('130', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.90/1.14       ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('split', [status(esa)], ['43'])).
% 0.90/1.14  thf('131', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['46', '50', '110', '130'])).
% 0.90/1.14  thf('132', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v4_pre_topc @ X0 @ sk_B)
% 0.90/1.14          | (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14              sk_C @ X0) @ 
% 0.90/1.14             sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['129', '131'])).
% 0.90/1.14  thf('133', plain,
% 0.90/1.14      (((v4_pre_topc @ 
% 0.90/1.14         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.90/1.14          (sk_D @ sk_C @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.90/1.14         sk_A)
% 0.90/1.14        | ~ (v4_pre_topc @ 
% 0.90/1.14             (sk_D @ sk_C @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.90/1.14              sk_A) @ 
% 0.90/1.14             sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['119', '132'])).
% 0.90/1.14  thf('134', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X0)
% 0.90/1.14          | (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('135', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (u1_struct_0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.14      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.14  thf('136', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | (v4_pre_topc @ (sk_D @ X2 @ X1 @ X3) @ X1)
% 0.90/1.14          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('137', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14             (u1_struct_0 @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v4_pre_topc @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['135', '136'])).
% 0.90/1.14  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('140', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14        (u1_struct_0 @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.14  thf('141', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v4_pre_topc @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (l1_pre_topc @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.90/1.14  thf('142', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.14        | (v4_pre_topc @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['134', '141'])).
% 0.90/1.14  thf('143', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('144', plain,
% 0.90/1.14      (((v4_pre_topc @ 
% 0.90/1.14         (sk_D @ sk_C @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['142', '143'])).
% 0.90/1.14  thf('145', plain,
% 0.90/1.14      ((m1_subset_1 @ 
% 0.90/1.14        (sk_D @ sk_C @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (u1_struct_0 @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.90/1.14      inference('clc', [status(thm)], ['36', '115'])).
% 0.90/1.14  thf('146', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i]:
% 0.90/1.14         (~ (v4_pre_topc @ X12 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (u1_struct_0 @ 
% 0.90/1.14                 (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))))
% 0.90/1.14          | (v4_pre_topc @ X12 @ X13)
% 0.90/1.14          | ~ (l1_pre_topc @ X13)
% 0.90/1.14          | ~ (v2_pre_topc @ X13))),
% 0.90/1.14      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.90/1.14  thf('147', plain,
% 0.90/1.14      ((~ (v2_pre_topc @ sk_B)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14        | (v4_pre_topc @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           sk_B)
% 0.90/1.14        | ~ (v4_pre_topc @ 
% 0.90/1.14             (sk_D @ sk_C @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.90/1.14              sk_A) @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['145', '146'])).
% 0.90/1.14  thf('148', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('149', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('150', plain,
% 0.90/1.14      (((v4_pre_topc @ 
% 0.90/1.14         (sk_D @ sk_C @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14         sk_B)
% 0.90/1.14        | ~ (v4_pre_topc @ 
% 0.90/1.14             (sk_D @ sk_C @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.90/1.14              sk_A) @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.90/1.14  thf('151', plain,
% 0.90/1.14      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v4_pre_topc @ 
% 0.90/1.14           (sk_D @ sk_C @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14           sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['144', '150'])).
% 0.90/1.14  thf('152', plain,
% 0.90/1.14      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['40', '114'])).
% 0.90/1.14  thf('153', plain,
% 0.90/1.14      ((v4_pre_topc @ 
% 0.90/1.14        (sk_D @ sk_C @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A) @ 
% 0.90/1.14        sk_B)),
% 0.90/1.14      inference('clc', [status(thm)], ['151', '152'])).
% 0.90/1.14  thf('154', plain,
% 0.90/1.14      ((v4_pre_topc @ 
% 0.90/1.14        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.90/1.14         (sk_D @ sk_C @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) @ 
% 0.90/1.14        sk_A)),
% 0.90/1.14      inference('demod', [status(thm)], ['133', '153'])).
% 0.90/1.14  thf('155', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((u1_struct_0 @ 
% 0.90/1.14            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14            = (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (l1_pre_topc @ X0))),
% 0.90/1.14      inference('clc', [status(thm)], ['12', '13'])).
% 0.90/1.14  thf('156', plain,
% 0.90/1.14      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v4_pre_topc @ 
% 0.90/1.14               (k8_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2 @ 
% 0.90/1.14                (sk_D @ X2 @ X1 @ X3)) @ 
% 0.90/1.14               X3)
% 0.90/1.14          | (v5_pre_topc @ X2 @ X3 @ X1)
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.90/1.14  thf('157', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (v4_pre_topc @ 
% 0.90/1.14             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2 @ 
% 0.90/1.14              (sk_D @ X2 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)) @ 
% 0.90/1.14             X1)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 0.90/1.14          | ~ (m1_subset_1 @ X2 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 0.90/1.14                 (u1_struct_0 @ 
% 0.90/1.14                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.90/1.14          | (v5_pre_topc @ X2 @ X1 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14          | ~ (l1_pre_topc @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['155', '156'])).
% 0.90/1.14  thf('158', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | ~ (m1_subset_1 @ sk_C @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14               (u1_struct_0 @ 
% 0.90/1.14                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14             (u1_struct_0 @ 
% 0.90/1.14              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['154', '157'])).
% 0.90/1.14  thf('159', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (u1_struct_0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.14      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.14  thf('160', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14        (u1_struct_0 @ 
% 0.90/1.14         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.14  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('163', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('164', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.14        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['158', '159', '160', '161', '162', '163'])).
% 0.90/1.14  thf('165', plain,
% 0.90/1.14      (~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['40', '114'])).
% 0.90/1.14  thf('166', plain,
% 0.90/1.14      (~ (l1_pre_topc @ 
% 0.90/1.14          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.14      inference('clc', [status(thm)], ['164', '165'])).
% 0.90/1.14  thf('167', plain, (~ (l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('sup-', [status(thm)], ['2', '166'])).
% 0.90/1.14  thf('168', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('169', plain, ($false), inference('demod', [status(thm)], ['167', '168'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
