%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mysdkh2nFr

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:40 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  261 (2497 expanded)
%              Number of leaves         :   41 ( 729 expanded)
%              Depth                    :   42
%              Number of atoms          : 4281 (68953 expanded)
%              Number of equality atoms :   69 (1377 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ D @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( r2_hidden @ F @ D )
                             => ( ( k3_funct_2 @ A @ B @ C @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( ( k2_partfun1 @ A @ B @ C @ D )
                          = E ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( sk_F @ X17 @ X15 @ X18 @ X14 @ X16 ) @ X16 )
      | ( ( k2_partfun1 @ X16 @ X14 @ X18 @ X15 )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
        = sk_C )
      | ( m1_subset_1 @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
        = sk_C )
      | ( m1_subset_1 @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) )
      = sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ( m1_pre_topc @ X36 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) @ X31 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('33',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','36','37','38','39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','26','47','48','49'])).

thf('51',plain,
    ( ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ X7 )
      | ( ( k3_funct_2 @ X7 @ X8 @ X6 @ X9 )
        = ( k1_funct_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k3_funct_2 @ X16 @ X14 @ X18 @ ( sk_F @ X17 @ X15 @ X18 @ X14 @ X16 ) )
       != ( k1_funct_1 @ X17 @ ( sk_F @ X17 @ X15 @ X18 @ X14 @ X16 ) ) )
      | ( ( k2_partfun1 @ X16 @ X14 @ X18 @ X15 )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('61',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) )
      = sk_C )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('69',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('70',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66','67','68','69'])).

thf('71',plain,
    ( ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('74',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( m1_subset_1 @ ( sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) @ ( k2_tmap_1 @ X39 @ X41 @ X40 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X39 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('90',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('95',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('103',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','100','108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','111'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('113',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('121',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( r2_hidden @ ( sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41 ) @ ( u1_struct_0 @ X43 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) @ ( k2_tmap_1 @ X39 @ X41 @ X40 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X39 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('130',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128','129','130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','131'])).

thf('133',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('134',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('135',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['120','137'])).

thf('139',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ X47 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( X47
        = ( k1_funct_1 @ sk_C @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','140'])).

thf('142',plain,
    ( ( ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('144',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['120','137'])).

thf(t95_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
               => ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C )
                  = C ) ) ) ) ) )).

thf('145',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ~ ( r2_hidden @ X46 @ ( u1_struct_0 @ X44 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X45 @ X44 ) @ X46 )
        = X46 )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X45 ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','111'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) @ X40 @ ( sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41 ) )
       != ( k1_funct_1 @ X42 @ ( sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) @ ( k2_tmap_1 @ X39 @ X41 @ X40 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X39 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('159',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('163',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('164',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('165',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('170',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('171',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164','165','166','167','168','169','170'])).

thf('172',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['153','172'])).

thf('174',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( sk_F_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['142','174'])).

thf('176',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['71','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('181',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( X10 = X13 )
      | ~ ( r2_funct_2 @ X11 @ X12 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('187',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('188',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('189',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['178','189'])).

thf('191',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( r2_funct_2 @ X11 @ X12 @ X10 @ X13 )
      | ( X10 != X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('195',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_funct_2 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['193','195'])).

thf('197',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','199'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('201',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('202',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('204',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('205',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['202','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('216',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['213','216'])).

thf('218',plain,(
    $false ),
    inference(demod,[status(thm)],['0','217'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mysdkh2nFr
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:42 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 170 iterations in 0.153s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.41/0.62  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.62  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.62  thf(t96_tmap_1, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.62                 ( m1_subset_1 @
% 0.41/0.62                   C @ 
% 0.41/0.62                   ( k1_zfmisc_1 @
% 0.41/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.62               ( ( ![D:$i]:
% 0.41/0.62                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.62                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.41/0.62                 ( r2_funct_2 @
% 0.41/0.62                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.62            ( l1_pre_topc @ A ) ) =>
% 0.41/0.62          ( ![B:$i]:
% 0.41/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.62              ( ![C:$i]:
% 0.41/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.62                    ( v1_funct_2 @
% 0.41/0.62                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.62                    ( m1_subset_1 @
% 0.41/0.62                      C @ 
% 0.41/0.62                      ( k1_zfmisc_1 @
% 0.41/0.62                        ( k2_zfmisc_1 @
% 0.41/0.62                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.62                  ( ( ![D:$i]:
% 0.41/0.62                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.62                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.41/0.62                    ( r2_funct_2 @
% 0.41/0.62                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 0.41/0.62  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t173_funct_2, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62               ( ![D:$i]:
% 0.41/0.62                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.62                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62                   ( ![E:$i]:
% 0.41/0.62                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ B ) & 
% 0.41/0.62                         ( m1_subset_1 @
% 0.41/0.62                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.41/0.62                       ( ( ![F:$i]:
% 0.41/0.62                           ( ( m1_subset_1 @ F @ A ) =>
% 0.41/0.62                             ( ( r2_hidden @ F @ D ) =>
% 0.41/0.62                               ( ( k3_funct_2 @ A @ B @ C @ F ) =
% 0.41/0.62                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.41/0.62                         ( ( k2_partfun1 @ A @ B @ C @ D ) = ( E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X14)
% 0.41/0.62          | (v1_xboole_0 @ X15)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.62          | (m1_subset_1 @ (sk_F @ X17 @ X15 @ X18 @ X14 @ X16) @ X16)
% 0.41/0.62          | ((k2_partfun1 @ X16 @ X14 @ X18 @ X15) = (X17))
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.41/0.62          | ~ (v1_funct_2 @ X17 @ X15 @ X14)
% 0.41/0.62          | ~ (v1_funct_1 @ X17)
% 0.41/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.41/0.62          | ~ (v1_funct_2 @ X18 @ X16 @ X14)
% 0.41/0.62          | ~ (v1_funct_1 @ X18)
% 0.41/0.62          | (v1_xboole_0 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X1)
% 0.41/0.62          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.41/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62               (u1_struct_0 @ sk_A))
% 0.41/0.62          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.41/0.62              (u1_struct_0 @ sk_B_1)) = (sk_C))
% 0.41/0.62          | (m1_subset_1 @ 
% 0.41/0.62             (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ X1 @ 
% 0.41/0.62              (u1_struct_0 @ sk_A) @ X0) @ 
% 0.41/0.62             X0)
% 0.41/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_zfmisc_1 @ X0))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X1)
% 0.41/0.62          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.41/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.41/0.62              (u1_struct_0 @ sk_B_1)) = (sk_C))
% 0.41/0.62          | (m1_subset_1 @ 
% 0.41/0.62             (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ X1 @ 
% 0.41/0.62              (u1_struct_0 @ sk_A) @ X0) @ 
% 0.41/0.62             X0)
% 0.41/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_zfmisc_1 @ X0))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ (u1_struct_0 @ sk_B_1)) = (sk_C))
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '7'])).
% 0.41/0.62  thf('9', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d10_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('11', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.41/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.62  thf(t4_tsep_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.62               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.41/0.62                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ X36 @ X37)
% 0.41/0.62          | ~ (r1_tarski @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 0.41/0.62          | (m1_pre_topc @ X36 @ X38)
% 0.41/0.62          | ~ (m1_pre_topc @ X38 @ X37)
% 0.41/0.62          | ~ (l1_pre_topc @ X37)
% 0.41/0.62          | ~ (v2_pre_topc @ X37))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v2_pre_topc @ X1)
% 0.41/0.62          | ~ (l1_pre_topc @ X1)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ X1)
% 0.41/0.62          | (m1_pre_topc @ X0 @ X0)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((m1_pre_topc @ X0 @ X0)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ X1)
% 0.41/0.62          | ~ (l1_pre_topc @ X1)
% 0.41/0.62          | ~ (v2_pre_topc @ X1))),
% 0.41/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      ((~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['9', '14'])).
% 0.41/0.62  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('18', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.41/0.62  thf(t1_tsep_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.62           ( m1_subset_1 @
% 0.41/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X34 : $i, X35 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ X34 @ X35)
% 0.41/0.62          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.41/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.41/0.62          | ~ (l1_pre_topc @ X35))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      ((~ (l1_pre_topc @ sk_B_1)
% 0.41/0.62        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_m1_pre_topc, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X22 : $i, X23 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.41/0.62          | (l1_pre_topc @ X22)
% 0.41/0.62          | ~ (l1_pre_topc @ X23))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.62  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.62  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('25', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.62  thf('27', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d4_tmap_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.62             ( l1_pre_topc @ B ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.62                 ( m1_subset_1 @
% 0.41/0.62                   C @ 
% 0.41/0.62                   ( k1_zfmisc_1 @
% 0.41/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.62               ( ![D:$i]:
% 0.41/0.62                 ( ( m1_pre_topc @ D @ A ) =>
% 0.41/0.62                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.41/0.62                     ( k2_partfun1 @
% 0.41/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.41/0.62                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X28)
% 0.41/0.62          | ~ (v2_pre_topc @ X28)
% 0.41/0.62          | ~ (l1_pre_topc @ X28)
% 0.41/0.62          | ~ (m1_pre_topc @ X29 @ X30)
% 0.41/0.62          | ((k2_tmap_1 @ X30 @ X28 @ X31 @ X29)
% 0.41/0.62              = (k2_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28) @ 
% 0.41/0.62                 X31 @ (u1_struct_0 @ X29)))
% 0.41/0.62          | ~ (m1_subset_1 @ X31 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 0.41/0.62          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 0.41/0.62          | ~ (v1_funct_1 @ X31)
% 0.41/0.62          | ~ (l1_pre_topc @ X30)
% 0.41/0.62          | ~ (v2_pre_topc @ X30)
% 0.41/0.62          | (v2_struct_0 @ X30))),
% 0.41/0.62      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_B_1)
% 0.41/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62               (u1_struct_0 @ sk_A))
% 0.41/0.62          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0)
% 0.41/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                 sk_C @ (u1_struct_0 @ X0)))
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.62  thf('31', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc1_pre_topc, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ X19 @ X20)
% 0.41/0.62          | (v2_pre_topc @ X19)
% 0.41/0.62          | ~ (l1_pre_topc @ X20)
% 0.41/0.62          | ~ (v2_pre_topc @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      ((~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | (v2_pre_topc @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.62  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('36', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.41/0.62  thf('37', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_B_1)
% 0.41/0.62          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0)
% 0.41/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                 sk_C @ (u1_struct_0 @ X0)))
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.62          | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)],
% 0.41/0.62                ['30', '36', '37', '38', '39', '40', '41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 0.41/0.62            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62               sk_C @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['27', '42'])).
% 0.41/0.62  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 0.41/0.62            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62               sk_C @ (u1_struct_0 @ sk_B_1))))),
% 0.41/0.62      inference('clc', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf('46', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 0.41/0.62         = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('clc', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['8', '26', '47', '48', '49'])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      ((((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k3_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.41/0.62         ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ A ) ) =>
% 0.41/0.62       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.41/0.62          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 0.41/0.62          | ~ (v1_funct_1 @ X6)
% 0.41/0.62          | (v1_xboole_0 @ X7)
% 0.41/0.62          | ~ (m1_subset_1 @ X9 @ X7)
% 0.41/0.62          | ((k3_funct_2 @ X7 @ X8 @ X6 @ X9) = (k1_funct_1 @ X6 @ X9)))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62               (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.62  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ 
% 0.41/0.62            (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62            = (k1_funct_1 @ sk_C @ 
% 0.41/0.62               (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['51', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      ((((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62          (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62          = (k1_funct_1 @ sk_C @ 
% 0.41/0.62             (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X14)
% 0.41/0.62          | (v1_xboole_0 @ X15)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.62          | ((k3_funct_2 @ X16 @ X14 @ X18 @ 
% 0.41/0.62              (sk_F @ X17 @ X15 @ X18 @ X14 @ X16))
% 0.41/0.62              != (k1_funct_1 @ X17 @ (sk_F @ X17 @ X15 @ X18 @ X14 @ X16)))
% 0.41/0.62          | ((k2_partfun1 @ X16 @ X14 @ X18 @ X15) = (X17))
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.41/0.62          | ~ (v1_funct_2 @ X17 @ X15 @ X14)
% 0.41/0.62          | ~ (v1_funct_1 @ X17)
% 0.41/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.41/0.62          | ~ (v1_funct_2 @ X18 @ X16 @ X14)
% 0.41/0.62          | ~ (v1_funct_1 @ X18)
% 0.41/0.62          | (v1_xboole_0 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.41/0.62  thf('61', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_C @ 
% 0.41/0.62          (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62          != (k1_funct_1 @ sk_C @ 
% 0.41/0.62              (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (m1_subset_1 @ sk_C @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (m1_subset_1 @ sk_C @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | ((k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ (u1_struct_0 @ sk_B_1)) = (sk_C))
% 0.41/0.62        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['59', '60'])).
% 0.41/0.62  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('67', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('68', plain,
% 0.41/0.62      (((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 0.41/0.62         = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('clc', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_C @ 
% 0.41/0.62          (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.62          != (k1_funct_1 @ sk_C @ 
% 0.41/0.62              (sk_F @ sk_C @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.41/0.62               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)],
% 0.41/0.62                ['61', '62', '63', '64', '65', '66', '67', '68', '69'])).
% 0.41/0.62  thf('71', plain,
% 0.41/0.62      ((((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.41/0.62  thf('72', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      ((((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.41/0.62  thf('74', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k4_tmap_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.62         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.62       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 0.41/0.62         ( v1_funct_2 @
% 0.41/0.62           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.62         ( m1_subset_1 @
% 0.41/0.62           ( k4_tmap_1 @ A @ B ) @ 
% 0.41/0.62           ( k1_zfmisc_1 @
% 0.41/0.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.62  thf('75', plain,
% 0.41/0.62      (![X32 : $i, X33 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X32)
% 0.41/0.62          | ~ (v2_pre_topc @ X32)
% 0.41/0.62          | (v2_struct_0 @ X32)
% 0.41/0.62          | ~ (m1_pre_topc @ X33 @ X32)
% 0.41/0.62          | (m1_subset_1 @ (k4_tmap_1 @ X32 @ X33) @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 0.41/0.62  thf('76', plain,
% 0.41/0.62      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62         (k1_zfmisc_1 @ 
% 0.41/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.41/0.62  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('79', plain,
% 0.41/0.62      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62         (k1_zfmisc_1 @ 
% 0.41/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.41/0.62  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('81', plain,
% 0.41/0.62      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('82', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t59_tmap_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.62             ( l1_pre_topc @ B ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.41/0.62               ( ![D:$i]:
% 0.41/0.62                 ( ( ( v1_funct_1 @ D ) & 
% 0.41/0.62                     ( v1_funct_2 @
% 0.41/0.62                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.62                     ( m1_subset_1 @
% 0.41/0.62                       D @ 
% 0.41/0.62                       ( k1_zfmisc_1 @
% 0.41/0.62                         ( k2_zfmisc_1 @
% 0.41/0.62                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.62                   ( ![E:$i]:
% 0.41/0.62                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.62                         ( v1_funct_2 @
% 0.41/0.62                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.62                         ( m1_subset_1 @
% 0.41/0.62                           E @ 
% 0.41/0.62                           ( k1_zfmisc_1 @
% 0.41/0.62                             ( k2_zfmisc_1 @
% 0.41/0.62                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.62                       ( ( ![F:$i]:
% 0.41/0.62                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.62                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.62                               ( ( k3_funct_2 @
% 0.41/0.62                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                                   D @ F ) =
% 0.41/0.62                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.41/0.62                         ( r2_funct_2 @
% 0.41/0.62                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('83', plain,
% 0.41/0.62      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X39)
% 0.41/0.62          | ~ (v2_pre_topc @ X39)
% 0.41/0.62          | ~ (l1_pre_topc @ X39)
% 0.41/0.62          | ~ (v1_funct_1 @ X40)
% 0.41/0.62          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))
% 0.41/0.62          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))))
% 0.41/0.62          | (m1_subset_1 @ (sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41) @ 
% 0.41/0.62             (u1_struct_0 @ X39))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41) @ 
% 0.41/0.62             (k2_tmap_1 @ X39 @ X41 @ X40 @ X43) @ X42)
% 0.41/0.62          | ~ (m1_subset_1 @ X42 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))))
% 0.41/0.62          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))
% 0.41/0.62          | ~ (v1_funct_1 @ X42)
% 0.41/0.62          | ~ (m1_pre_topc @ X43 @ X39)
% 0.41/0.62          | (v2_struct_0 @ X43)
% 0.41/0.62          | ~ (l1_pre_topc @ X41)
% 0.41/0.62          | ~ (v2_pre_topc @ X41)
% 0.41/0.62          | (v2_struct_0 @ X41))),
% 0.41/0.62      inference('cnf', [status(esa)], [t59_tmap_1])).
% 0.41/0.62  thf('84', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_A)
% 0.41/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.62          | ~ (v1_funct_1 @ X1)
% 0.41/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.41/0.62          | (m1_subset_1 @ (sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62               (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.62  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('87', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('89', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('90', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.41/0.62  thf('91', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.62          | ~ (v1_funct_1 @ X1)
% 0.41/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.41/0.62          | (m1_subset_1 @ (sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)],
% 0.41/0.62                ['84', '85', '86', '87', '88', '89', '90'])).
% 0.41/0.62  thf('92', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['81', '91'])).
% 0.41/0.62  thf('93', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('94', plain,
% 0.41/0.62      (![X32 : $i, X33 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X32)
% 0.41/0.62          | ~ (v2_pre_topc @ X32)
% 0.41/0.62          | (v2_struct_0 @ X32)
% 0.41/0.62          | ~ (m1_pre_topc @ X33 @ X32)
% 0.41/0.62          | (v1_funct_2 @ (k4_tmap_1 @ X32 @ X33) @ (u1_struct_0 @ X33) @ 
% 0.41/0.62             (u1_struct_0 @ X32)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 0.41/0.62  thf('95', plain,
% 0.41/0.62      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62         (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['93', '94'])).
% 0.41/0.62  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('98', plain,
% 0.41/0.62      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62         (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.41/0.62  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('100', plain,
% 0.41/0.62      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62        (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.41/0.62  thf('101', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('102', plain,
% 0.41/0.62      (![X32 : $i, X33 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X32)
% 0.41/0.62          | ~ (v2_pre_topc @ X32)
% 0.41/0.62          | (v2_struct_0 @ X32)
% 0.41/0.62          | ~ (m1_pre_topc @ X33 @ X32)
% 0.41/0.62          | (v1_funct_1 @ (k4_tmap_1 @ X32 @ X33)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 0.41/0.62  thf('103', plain,
% 0.41/0.62      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['101', '102'])).
% 0.41/0.62  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('106', plain,
% 0.41/0.62      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.41/0.62  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('108', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 0.41/0.62      inference('clc', [status(thm)], ['106', '107'])).
% 0.41/0.62  thf('109', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.41/0.62  thf('110', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['92', '100', '108', '109'])).
% 0.41/0.62  thf('111', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('simplify', [status(thm)], ['110'])).
% 0.41/0.62  thf('112', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['73', '111'])).
% 0.41/0.62  thf(t55_pre_topc, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.62               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.41/0.62  thf('113', plain,
% 0.41/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X25)
% 0.41/0.62          | ~ (m1_pre_topc @ X25 @ X26)
% 0.41/0.62          | (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.41/0.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.41/0.62          | ~ (l1_pre_topc @ X26)
% 0.41/0.62          | (v2_struct_0 @ X26))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.41/0.62  thf('114', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ sk_B_1)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | (m1_subset_1 @ 
% 0.41/0.62             (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.41/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['112', '113'])).
% 0.41/0.62  thf('115', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.41/0.62          | (m1_subset_1 @ 
% 0.41/0.62             (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v2_struct_0 @ sk_B_1)
% 0.41/0.62          | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['114'])).
% 0.41/0.62  thf('116', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['72', '115'])).
% 0.41/0.62  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('118', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['116', '117'])).
% 0.41/0.62  thf('119', plain,
% 0.41/0.62      (((m1_subset_1 @ 
% 0.41/0.62         (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 0.41/0.62         (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['118'])).
% 0.41/0.62  thf('120', plain,
% 0.41/0.62      ((((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) = (sk_C))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.41/0.62  thf('121', plain,
% 0.41/0.62      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('122', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('123', plain,
% 0.41/0.62      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X39)
% 0.41/0.62          | ~ (v2_pre_topc @ X39)
% 0.41/0.62          | ~ (l1_pre_topc @ X39)
% 0.41/0.62          | ~ (v1_funct_1 @ X40)
% 0.41/0.62          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))
% 0.41/0.62          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))))
% 0.41/0.62          | (r2_hidden @ (sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41) @ 
% 0.41/0.62             (u1_struct_0 @ X43))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41) @ 
% 0.41/0.62             (k2_tmap_1 @ X39 @ X41 @ X40 @ X43) @ X42)
% 0.41/0.62          | ~ (m1_subset_1 @ X42 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))))
% 0.41/0.62          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))
% 0.41/0.62          | ~ (v1_funct_1 @ X42)
% 0.41/0.62          | ~ (m1_pre_topc @ X43 @ X39)
% 0.41/0.62          | (v2_struct_0 @ X43)
% 0.41/0.62          | ~ (l1_pre_topc @ X41)
% 0.41/0.62          | ~ (v2_pre_topc @ X41)
% 0.41/0.62          | (v2_struct_0 @ X41))),
% 0.41/0.62      inference('cnf', [status(esa)], [t59_tmap_1])).
% 0.41/0.62  thf('124', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_A)
% 0.41/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.62          | ~ (v1_funct_1 @ X1)
% 0.41/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.41/0.62          | (r2_hidden @ (sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62               (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['122', '123'])).
% 0.41/0.62  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('127', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('129', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('130', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.41/0.62  thf('131', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.62          | ~ (v1_funct_1 @ X1)
% 0.41/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.41/0.62          | (r2_hidden @ (sk_F_1 @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ X0))
% 0.41/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)],
% 0.41/0.62                ['124', '125', '126', '127', '128', '129', '130'])).
% 0.41/0.62  thf('132', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['121', '131'])).
% 0.41/0.62  thf('133', plain,
% 0.41/0.62      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62        (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.41/0.62  thf('134', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 0.41/0.62      inference('clc', [status(thm)], ['106', '107'])).
% 0.41/0.62  thf('135', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.41/0.62  thf('136', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 0.41/0.62  thf('137', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (r2_hidden @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('simplify', [status(thm)], ['136'])).
% 0.41/0.62  thf('138', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['120', '137'])).
% 0.41/0.62  thf('139', plain,
% 0.41/0.62      (![X47 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X47 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | ((X47) = (k1_funct_1 @ sk_C @ X47))
% 0.41/0.62          | ~ (m1_subset_1 @ X47 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('140', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (m1_subset_1 @ 
% 0.41/0.62             (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A) @ 
% 0.41/0.62             (u1_struct_0 @ sk_A))
% 0.41/0.62        | ((sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A)
% 0.41/0.62            = (k1_funct_1 @ sk_C @ 
% 0.41/0.62               (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                sk_B_1 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['138', '139'])).
% 0.41/0.62  thf('141', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ((sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A)
% 0.41/0.62            = (k1_funct_1 @ sk_C @ 
% 0.41/0.62               (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                sk_B_1 @ sk_A)))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['119', '140'])).
% 0.41/0.62  thf('142', plain,
% 0.41/0.62      ((((sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A)
% 0.41/0.62          = (k1_funct_1 @ sk_C @ 
% 0.41/0.62             (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A)))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['141'])).
% 0.41/0.62  thf('143', plain,
% 0.41/0.62      (((m1_subset_1 @ 
% 0.41/0.62         (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 0.41/0.62         (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['118'])).
% 0.41/0.62  thf('144', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['120', '137'])).
% 0.41/0.62  thf(t95_tmap_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.62                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('145', plain,
% 0.41/0.62      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X44)
% 0.41/0.62          | ~ (m1_pre_topc @ X44 @ X45)
% 0.41/0.62          | ~ (r2_hidden @ X46 @ (u1_struct_0 @ X44))
% 0.41/0.62          | ((k1_funct_1 @ (k4_tmap_1 @ X45 @ X44) @ X46) = (X46))
% 0.41/0.62          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X45))
% 0.41/0.62          | ~ (l1_pre_topc @ X45)
% 0.41/0.62          | ~ (v2_pre_topc @ X45)
% 0.41/0.62          | (v2_struct_0 @ X45))),
% 0.41/0.62      inference('cnf', [status(esa)], [t95_tmap_1])).
% 0.41/0.62  thf('146', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_struct_0 @ sk_A)
% 0.41/0.62          | (v2_struct_0 @ sk_B_1)
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | ~ (m1_subset_1 @ 
% 0.41/0.62               (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                sk_B_1 @ sk_A) @ 
% 0.41/0.62               (u1_struct_0 @ X0))
% 0.41/0.62          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 0.41/0.62              (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62               sk_A))
% 0.41/0.62              = (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                 sk_B_1 @ sk_A))
% 0.41/0.62          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.41/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['144', '145'])).
% 0.41/0.62  thf('147', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.41/0.62          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 0.41/0.62              (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62               sk_A))
% 0.41/0.62              = (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                 sk_B_1 @ sk_A))
% 0.41/0.62          | ~ (m1_subset_1 @ 
% 0.41/0.62               (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                sk_B_1 @ sk_A) @ 
% 0.41/0.62               (u1_struct_0 @ X0))
% 0.41/0.62          | ~ (l1_pre_topc @ X0)
% 0.41/0.62          | ~ (v2_pre_topc @ X0)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v2_struct_0 @ sk_B_1)
% 0.41/0.62          | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['146'])).
% 0.41/0.62  thf('148', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62            (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62             sk_A))
% 0.41/0.62            = (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62               sk_A))
% 0.41/0.62        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['143', '147'])).
% 0.41/0.62  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('151', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('152', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62            (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62             sk_A))
% 0.41/0.62            = (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62               sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 0.41/0.62  thf('153', plain,
% 0.41/0.62      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62          (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 0.41/0.62          = (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62             sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['152'])).
% 0.41/0.62  thf('154', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (m1_subset_1 @ 
% 0.41/0.62           (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62            sk_A) @ 
% 0.41/0.62           (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['73', '111'])).
% 0.41/0.62  thf('155', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.62  thf('156', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | ((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            sk_C @ 
% 0.41/0.62            (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62             sk_A))
% 0.41/0.62            = (k1_funct_1 @ sk_C @ 
% 0.41/0.62               (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                sk_B_1 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['154', '155'])).
% 0.41/0.62  thf('157', plain,
% 0.41/0.62      ((((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62          (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 0.41/0.62          = (k1_funct_1 @ sk_C @ 
% 0.41/0.62             (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A)))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['156'])).
% 0.41/0.62  thf('158', plain,
% 0.41/0.62      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X39)
% 0.41/0.62          | ~ (v2_pre_topc @ X39)
% 0.41/0.62          | ~ (l1_pre_topc @ X39)
% 0.41/0.62          | ~ (v1_funct_1 @ X40)
% 0.41/0.62          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))
% 0.41/0.62          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))))
% 0.41/0.62          | ((k3_funct_2 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41) @ X40 @ 
% 0.41/0.62              (sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41))
% 0.41/0.62              != (k1_funct_1 @ X42 @ (sk_F_1 @ X42 @ X40 @ X43 @ X39 @ X41)))
% 0.41/0.62          | (r2_funct_2 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41) @ 
% 0.41/0.62             (k2_tmap_1 @ X39 @ X41 @ X40 @ X43) @ X42)
% 0.41/0.62          | ~ (m1_subset_1 @ X42 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))))
% 0.41/0.62          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))
% 0.41/0.62          | ~ (v1_funct_1 @ X42)
% 0.41/0.62          | ~ (m1_pre_topc @ X43 @ X39)
% 0.41/0.62          | (v2_struct_0 @ X43)
% 0.41/0.62          | ~ (l1_pre_topc @ X41)
% 0.41/0.62          | ~ (v2_pre_topc @ X41)
% 0.41/0.62          | (v2_struct_0 @ X41))),
% 0.41/0.62      inference('cnf', [status(esa)], [t59_tmap_1])).
% 0.41/0.62  thf('159', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_C @ 
% 0.41/0.62          (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 0.41/0.62          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62              (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62               sk_A)))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (m1_subset_1 @ sk_C @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['157', '158'])).
% 0.41/0.62  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('162', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.41/0.62  thf('163', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 0.41/0.62      inference('clc', [status(thm)], ['106', '107'])).
% 0.41/0.62  thf('164', plain,
% 0.41/0.62      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62        (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.41/0.62  thf('165', plain,
% 0.41/0.62      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('166', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('167', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('169', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('170', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.41/0.62  thf('171', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_C @ 
% 0.41/0.62          (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 0.41/0.62          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62              (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62               sk_A)))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)],
% 0.41/0.62                ['159', '160', '161', '162', '163', '164', '165', '166', 
% 0.41/0.62                 '167', '168', '169', '170'])).
% 0.41/0.62  thf('172', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62         (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ((k1_funct_1 @ sk_C @ 
% 0.41/0.62            (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62             sk_A))
% 0.41/0.62            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62                (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                 sk_B_1 @ sk_A))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['171'])).
% 0.41/0.62  thf('173', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_C @ 
% 0.41/0.62          (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 0.41/0.62          != (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['153', '172'])).
% 0.41/0.62  thf('174', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62         (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ((k1_funct_1 @ sk_C @ 
% 0.41/0.62            (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62             sk_A))
% 0.41/0.62            != (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ 
% 0.41/0.62                sk_B_1 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['173'])).
% 0.41/0.62  thf('175', plain,
% 0.41/0.62      ((((sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A)
% 0.41/0.62          != (sk_F_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 0.41/0.62              sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['142', '174'])).
% 0.41/0.62  thf('176', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62         (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('simplify', [status(thm)], ['175'])).
% 0.41/0.62  thf('177', plain,
% 0.41/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62         (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['71', '176'])).
% 0.41/0.62  thf('178', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['177'])).
% 0.41/0.62  thf('179', plain,
% 0.41/0.62      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('180', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_r2_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.41/0.62  thf('181', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.41/0.62          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.41/0.62          | ~ (v1_funct_1 @ X10)
% 0.41/0.62          | ~ (v1_funct_1 @ X13)
% 0.41/0.62          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.41/0.62          | ((X10) = (X13))
% 0.41/0.62          | ~ (r2_funct_2 @ X11 @ X12 @ X10 @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.41/0.62  thf('182', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ X0)
% 0.41/0.62          | ((sk_C) = (X0))
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62               (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['180', '181'])).
% 0.41/0.62  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('184', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('185', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ X0)
% 0.41/0.62          | ((sk_C) = (X0))
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ 
% 0.41/0.62               (k1_zfmisc_1 @ 
% 0.41/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.41/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62          | ~ (v1_funct_1 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['182', '183', '184'])).
% 0.41/0.62  thf('186', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['179', '185'])).
% 0.41/0.62  thf('187', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 0.41/0.62      inference('clc', [status(thm)], ['106', '107'])).
% 0.41/0.62  thf('188', plain,
% 0.41/0.62      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.62        (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.41/0.62  thf('189', plain,
% 0.41/0.62      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.41/0.62  thf('190', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['178', '189'])).
% 0.41/0.62  thf('191', plain,
% 0.41/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('192', plain,
% 0.41/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           sk_C)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['190', '191'])).
% 0.41/0.62  thf('193', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('194', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.41/0.62          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.41/0.62          | ~ (v1_funct_1 @ X10)
% 0.41/0.62          | ~ (v1_funct_1 @ X13)
% 0.41/0.62          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.41/0.62          | (r2_funct_2 @ X11 @ X12 @ X10 @ X13)
% 0.41/0.62          | ((X10) != (X13)))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.41/0.62  thf('195', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         ((r2_funct_2 @ X11 @ X12 @ X13 @ X13)
% 0.41/0.62          | ~ (v1_funct_1 @ X13)
% 0.41/0.62          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['194'])).
% 0.41/0.62  thf('196', plain,
% 0.41/0.62      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62           sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['193', '195'])).
% 0.41/0.62  thf('197', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('199', plain,
% 0.41/0.62      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.41/0.62        sk_C)),
% 0.41/0.62      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.41/0.62  thf('200', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['192', '199'])).
% 0.41/0.62  thf(fc2_struct_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.62  thf('201', plain,
% 0.41/0.62      (![X24 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.41/0.62          | ~ (l1_struct_0 @ X24)
% 0.41/0.62          | (v2_struct_0 @ X24))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.62  thf('202', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['200', '201'])).
% 0.41/0.62  thf('203', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf(dt_l1_pre_topc, axiom,
% 0.41/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.62  thf('204', plain,
% 0.41/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.62  thf('205', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['203', '204'])).
% 0.41/0.62  thf('206', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['202', '205'])).
% 0.41/0.62  thf('207', plain,
% 0.41/0.62      (((v2_struct_0 @ sk_B_1)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['206'])).
% 0.41/0.62  thf('208', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('209', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['207', '208'])).
% 0.41/0.62  thf('210', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('211', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['209', '210'])).
% 0.41/0.62  thf('212', plain,
% 0.41/0.62      (![X24 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.41/0.62          | ~ (l1_struct_0 @ X24)
% 0.41/0.62          | (v2_struct_0 @ X24))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.62  thf('213', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['211', '212'])).
% 0.41/0.62  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('215', plain,
% 0.41/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.62  thf('216', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['214', '215'])).
% 0.41/0.62  thf('217', plain, ((v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['213', '216'])).
% 0.41/0.62  thf('218', plain, ($false), inference('demod', [status(thm)], ['0', '217'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
