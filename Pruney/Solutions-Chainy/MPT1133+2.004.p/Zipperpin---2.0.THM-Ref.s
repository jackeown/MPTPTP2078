%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O4Ptd5HahM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 944 expanded)
%              Number of leaves         :   24 ( 285 expanded)
%              Depth                    :   25
%              Number of atoms          : 2374 (29771 expanded)
%              Number of equality atoms :   29 ( 554 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ X11 @ X9 )
      | ( v5_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) @ X9 )
      | ( X12 != X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) @ X9 )
      | ~ ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_pre_topc @ X7 @ X8 )
       != ( g1_pre_topc @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','13','29','34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t63_pre_topc,axiom,(
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

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X16 @ X15 @ X13 )
      | ( v5_pre_topc @ X14 @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( X16 != X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v5_pre_topc @ X14 @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( v5_pre_topc @ X14 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46','47','48','49'])).

thf('54',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X14 @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( v5_pre_topc @ X16 @ X15 @ X13 )
      | ( X16 != X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v5_pre_topc @ X14 @ X15 @ X13 )
      | ~ ( v5_pre_topc @ X14 @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64','65','66'])).

thf('68',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,(
    ! [X4: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('84',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('85',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) @ X9 )
      | ( v5_pre_topc @ X12 @ X11 @ X9 )
      | ( X12 != X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('89',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ~ ( v5_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96'])).

thf('98',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64','65','66'])).

thf('107',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('109',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['71'])).

thf('111',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['77','81','109','110'])).

thf('112',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['68','111'])).

thf('113',plain,(
    v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','112'])).

thf('114',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','113'])).

thf('115',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('116',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('117',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['80'])).

thf('118',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['77','81','109','118'])).

thf('120',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['115','119'])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['114','120'])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['125','126','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O4Ptd5HahM
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 155 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(fc6_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ( v1_pre_topc @
% 0.20/0.52           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.52         ( v2_pre_topc @
% 0.20/0.52           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X4 : $i]:
% 0.20/0.52         ((v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.20/0.52          | ~ (l1_pre_topc @ X4)
% 0.20/0.52          | ~ (v2_pre_topc @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.20/0.52  thf(dt_u1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( u1_pre_topc @ A ) @ 
% 0.20/0.52         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X3 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.20/0.52          | ~ (l1_pre_topc @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf(dt_g1_pre_topc, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.20/0.52         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t64_pre_topc, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.52                     ( v1_funct_2 @
% 0.20/0.52                       D @ 
% 0.20/0.52                       ( u1_struct_0 @
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.20/0.52                       ( u1_struct_0 @
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.20/0.52                     ( m1_subset_1 @
% 0.20/0.52                       D @ 
% 0.20/0.52                       ( k1_zfmisc_1 @
% 0.20/0.52                         ( k2_zfmisc_1 @
% 0.20/0.52                           ( u1_struct_0 @
% 0.20/0.52                             ( g1_pre_topc @
% 0.20/0.52                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.20/0.52                           ( u1_struct_0 @
% 0.20/0.52                             ( g1_pre_topc @
% 0.20/0.52                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.20/0.52                   ( ( ( C ) = ( D ) ) =>
% 0.20/0.52                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.52                       ( v5_pre_topc @
% 0.20/0.52                         D @ 
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                    ( v1_funct_2 @
% 0.20/0.52                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                    ( m1_subset_1 @
% 0.20/0.52                      C @ 
% 0.20/0.52                      ( k1_zfmisc_1 @
% 0.20/0.52                        ( k2_zfmisc_1 @
% 0.20/0.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.52                        ( v1_funct_2 @
% 0.20/0.52                          D @ 
% 0.20/0.52                          ( u1_struct_0 @
% 0.20/0.52                            ( g1_pre_topc @
% 0.20/0.52                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.20/0.52                          ( u1_struct_0 @
% 0.20/0.52                            ( g1_pre_topc @
% 0.20/0.52                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.20/0.52                        ( m1_subset_1 @
% 0.20/0.52                          D @ 
% 0.20/0.52                          ( k1_zfmisc_1 @
% 0.20/0.52                            ( k2_zfmisc_1 @
% 0.20/0.52                              ( u1_struct_0 @
% 0.20/0.52                                ( g1_pre_topc @
% 0.20/0.52                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.20/0.52                              ( u1_struct_0 @
% 0.20/0.52                                ( g1_pre_topc @
% 0.20/0.52                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.20/0.52                      ( ( ( C ) = ( D ) ) =>
% 0.20/0.52                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.52                          ( v5_pre_topc @
% 0.20/0.52                            D @ 
% 0.20/0.52                            ( g1_pre_topc @
% 0.20/0.52                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.20/0.52                            ( g1_pre_topc @
% 0.20/0.52                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(t62_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.52                     ( v1_funct_2 @
% 0.20/0.52                       D @ 
% 0.20/0.52                       ( u1_struct_0 @
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.20/0.52                       ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                     ( m1_subset_1 @
% 0.20/0.52                       D @ 
% 0.20/0.52                       ( k1_zfmisc_1 @
% 0.20/0.52                         ( k2_zfmisc_1 @
% 0.20/0.52                           ( u1_struct_0 @
% 0.20/0.52                             ( g1_pre_topc @
% 0.20/0.52                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.20/0.52                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                   ( ( ( C ) = ( D ) ) =>
% 0.20/0.52                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.52                       ( v5_pre_topc @
% 0.20/0.52                         D @ 
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.20/0.52                         B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v1_funct_1 @ X10)
% 0.20/0.52          | ~ (v1_funct_2 @ X10 @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52               (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52                 (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v5_pre_topc @ X12 @ X11 @ X9)
% 0.20/0.52          | (v5_pre_topc @ X10 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)) @ X9)
% 0.20/0.52          | ((X12) != (X10))
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X12)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t62_pre_topc])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.20/0.52          | (v5_pre_topc @ X10 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)) @ X9)
% 0.20/0.52          | ~ (v5_pre_topc @ X10 @ X11 @ X9)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52                 (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X10 @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52               (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X10)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9))),
% 0.20/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_C @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.52  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_D @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X3 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.20/0.52          | ~ (l1_pre_topc @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ( v1_pre_topc @ A ) =>
% 0.20/0.52         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_pre_topc @ X0)
% 0.20/0.52          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X3 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.20/0.52          | ~ (l1_pre_topc @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf(free_g1_pre_topc, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i,D:$i]:
% 0.20/0.52         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.52           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (((g1_pre_topc @ X7 @ X8) != (g1_pre_topc @ X5 @ X6))
% 0.20/0.52          | ((X7) = (X5))
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.52      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.52              != (g1_pre_topc @ X1 @ X2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_pre_topc @ X0)
% 0.20/0.52          | ((u1_struct_0 @ X0) = (X2))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.20/0.52          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.20/0.52          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ((u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52              = (u1_struct_0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((u1_struct_0 @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52            = (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_C @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52           (u1_struct_0 @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((u1_struct_0 @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52            = (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (u1_struct_0 @ 
% 0.20/0.52          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['9', '10', '13', '29', '34', '35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf(t63_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.52                     ( v1_funct_2 @
% 0.20/0.52                       D @ ( u1_struct_0 @ A ) @ 
% 0.20/0.52                       ( u1_struct_0 @
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.20/0.52                     ( m1_subset_1 @
% 0.20/0.52                       D @ 
% 0.20/0.52                       ( k1_zfmisc_1 @
% 0.20/0.52                         ( k2_zfmisc_1 @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ 
% 0.20/0.52                           ( u1_struct_0 @
% 0.20/0.52                             ( g1_pre_topc @
% 0.20/0.52                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.20/0.52                   ( ( ( C ) = ( D ) ) =>
% 0.20/0.52                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.20/0.52                       ( v5_pre_topc @
% 0.20/0.52                         D @ A @ 
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))))
% 0.20/0.52          | ~ (v5_pre_topc @ X16 @ X15 @ X13)
% 0.20/0.52          | (v5_pre_topc @ X14 @ X15 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.20/0.52          | ((X16) != (X14))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.20/0.52          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.20/0.52          | ~ (v1_funct_1 @ X16)
% 0.20/0.52          | ~ (l1_pre_topc @ X15)
% 0.20/0.52          | ~ (v2_pre_topc @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t63_pre_topc])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X15)
% 0.20/0.52          | ~ (l1_pre_topc @ X15)
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.20/0.52          | (v5_pre_topc @ X14 @ X15 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.20/0.52          | ~ (v5_pre_topc @ X14 @ X15 @ X13)
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))))
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (v2_pre_topc @ X13))),
% 0.20/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_B)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_C @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '40'])).
% 0.20/0.52  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['41', '42', '43', '44', '45', '46', '47', '48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.52         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['41', '42', '43', '44', '45', '46', '47', '48', '49'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))))
% 0.20/0.52          | ~ (v5_pre_topc @ X14 @ X15 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.20/0.52          | (v5_pre_topc @ X16 @ X15 @ X13)
% 0.20/0.52          | ((X16) != (X14))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.20/0.52          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.20/0.52          | ~ (v1_funct_1 @ X16)
% 0.20/0.52          | ~ (l1_pre_topc @ X15)
% 0.20/0.52          | ~ (v2_pre_topc @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t63_pre_topc])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X15)
% 0.20/0.52          | ~ (l1_pre_topc @ X15)
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.20/0.52          | (v5_pre_topc @ X14 @ X15 @ X13)
% 0.20/0.52          | ~ (v5_pre_topc @ X14 @ X15 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))))
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (v2_pre_topc @ X13))),
% 0.20/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_B)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.52        | ~ (m1_subset_1 @ sk_C @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.52  thf('59', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['58', '59', '60', '61', '62', '63', '64', '65', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.52         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('70', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_C @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_D @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_D @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['73'])).
% 0.20/0.52  thf('75', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.52       ((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['72', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_D @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('79', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.52       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('split', [status(esa)], ['80'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (![X4 : $i]:
% 0.20/0.52         ((v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.20/0.52          | ~ (l1_pre_topc @ X4)
% 0.20/0.52          | ~ (v2_pre_topc @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['51'])).
% 0.20/0.52  thf('85', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v1_funct_1 @ X10)
% 0.20/0.52          | ~ (v1_funct_2 @ X10 @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52               (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52                 (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v5_pre_topc @ X10 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)) @ X9)
% 0.20/0.52          | (v5_pre_topc @ X12 @ X11 @ X9)
% 0.20/0.52          | ((X12) != (X10))
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X12)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t62_pre_topc])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.20/0.52          | (v5_pre_topc @ X10 @ X11 @ X9)
% 0.20/0.52          | ~ (v5_pre_topc @ X10 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)) @ X9)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ 
% 0.20/0.52                 (u1_struct_0 @ 
% 0.20/0.52                  (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52                 (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X10 @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))) @ 
% 0.20/0.52               (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X10)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9))),
% 0.20/0.52      inference('simplify', [status(thm)], ['88'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_C @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               (u1_struct_0 @ 
% 0.20/0.52                (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['87', '89'])).
% 0.20/0.52  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52          (u1_struct_0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52        (u1_struct_0 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['90', '91', '92', '93', '94', '95', '96'])).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52         | ~ (l1_pre_topc @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52         | ~ (v2_pre_topc @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['86', '97'])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.52         | ~ (v2_pre_topc @ 
% 0.20/0.52              (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '98'])).
% 0.20/0.52  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('101', plain,
% 0.20/0.52      (((~ (v2_pre_topc @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.52  thf('102', plain,
% 0.20/0.52      (((~ (v2_pre_topc @ sk_B)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['82', '101'])).
% 0.20/0.52  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.20/0.52  thf('106', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['58', '59', '60', '61', '62', '63', '64', '65', '66'])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.20/0.52         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['73'])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.52       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.20/0.52       ((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['71'])).
% 0.20/0.52  thf('111', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['77', '81', '109', '110'])).
% 0.20/0.52  thf('112', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['68', '111'])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      ((v5_pre_topc @ sk_C @ sk_A @ 
% 0.20/0.52        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['50', '112'])).
% 0.20/0.52  thf('114', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '113'])).
% 0.20/0.52  thf('115', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('116', plain,
% 0.20/0.52      (((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((v5_pre_topc @ sk_D @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('117', plain,
% 0.20/0.52      ((~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((v5_pre_topc @ sk_C @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['80'])).
% 0.20/0.52  thf('118', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.52       ((v5_pre_topc @ sk_C @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['116', '117'])).
% 0.20/0.52  thf('119', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((v5_pre_topc @ sk_D @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['77', '81', '109', '118'])).
% 0.20/0.52  thf('120', plain,
% 0.20/0.52      (~ (v5_pre_topc @ sk_C @ 
% 0.20/0.52          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.52          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['115', '119'])).
% 0.20/0.52  thf('121', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (v2_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('clc', [status(thm)], ['114', '120'])).
% 0.20/0.52  thf('122', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.52        | ~ (v2_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '121'])).
% 0.20/0.52  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('124', plain,
% 0.20/0.52      (~ (v2_pre_topc @ 
% 0.20/0.52          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['122', '123'])).
% 0.20/0.52  thf('125', plain, ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '124'])).
% 0.20/0.52  thf('126', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('127', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('128', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
