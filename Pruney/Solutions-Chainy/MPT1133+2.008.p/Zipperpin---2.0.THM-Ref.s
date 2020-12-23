%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AWh9gI8Qwn

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:28 EST 2020

% Result     : Theorem 4.38s
% Output     : Refutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  615 (67799962 expanded)
%              Number of leaves         :   52 (19408612 expanded)
%              Depth                    :   83
%              Number of atoms          : 10292 (2082723302 expanded)
%              Number of equality atoms :  293 (44980828 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X44 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X42 ) ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v5_pre_topc @ X49 @ X48 @ X46 )
      | ( v5_pre_topc @ X47 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) @ X46 )
      | ( X49 != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('8',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) @ X46 )
      | ~ ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','13','14','15'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('18',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('20',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['20'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('24',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( v1_partfun1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('25',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ( v1_partfun1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('31',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['42','44','45'])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

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

thf('55',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v2_pre_topc @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X53 @ X52 @ X50 )
      | ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ( X53 != X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( v1_funct_2 @ X53 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('56',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ~ ( v5_pre_topc @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ X1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ X1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66'])).

thf('68',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('70',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('71',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_partfun1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X33 )
       != X32 )
      | ( v1_partfun1 @ X33 @ X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('80',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v4_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) )
      | ( v1_partfun1 @ X33 @ ( k1_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( v1_partfun1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('83',plain,(
    v1_partfun1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','83','84'])).

thf('86',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['68','85'])).

thf('87',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','87'])).

thf('89',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('103',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('104',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('106',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('107',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('108',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('109',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('112',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('113',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v5_pre_topc @ X47 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) @ X46 )
      | ( v5_pre_topc @ X49 @ X48 @ X46 )
      | ( X49 != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('114',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( v5_pre_topc @ X47 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('123',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['110','123'])).

thf('125',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['107','124'])).

thf('126',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','83','84'])).

thf('127',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['105','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('137',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('138',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('139',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v2_pre_topc @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ( v5_pre_topc @ X53 @ X52 @ X50 )
      | ( X53 != X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( v1_funct_2 @ X53 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('140',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v5_pre_topc @ X51 @ X52 @ X50 )
      | ~ ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146','147','148','149','150'])).

thf('152',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['136','151'])).

thf('153',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','83','84'])).

thf('154',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['135','155'])).

thf('157',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('159',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('161',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('164',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('165',plain,(
    ! [X36: $i,X37: $i] :
      ( m1_subset_1 @ ( sk_C @ X36 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('166',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','170'])).

thf('172',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_funct_1 @ ( sk_C @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('173',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['162','173'])).

thf('175',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['159','174'])).

thf('176',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('177',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ( v1_funct_2 @ sk_C_1 @ X0 @ X1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_B_1 )
          = k1_xboole_0 )
        | ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','177'])).

thf('179',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('180',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_B_1 )
          = sk_C_1 )
        | ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('182',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('183',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('185',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('187',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['180','187'])).

thf('189',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','188'])).

thf('190',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','192'])).

thf('194',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('197',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('198',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('200',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('201',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('202',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('203',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v5_pre_topc @ X51 @ X52 @ X50 )
      | ~ ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('204',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('209',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207','208'])).

thf('210',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['201','209'])).

thf('211',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('212',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['200','212'])).

thf('214',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('215',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','170'])).

thf('217',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_funct_2 @ ( sk_C @ X36 @ X37 ) @ X37 @ X36 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('218',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['215','218'])).

thf('220',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('221',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('223',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('224',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('225',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('226',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['224','227'])).

thf('229',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('230',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['223','230'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('232',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('233',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('234',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X34 ) @ X34 ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['231','234'])).

thf('236',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('237',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('239',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('240',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('242',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('243',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['237','240','243'])).

thf('245',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['222','244'])).

thf('246',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('247',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['213','214','221','247'])).

thf('249',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['199','248'])).

thf('250',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['198','251'])).

thf('253',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('257',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ( v1_partfun1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('258',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('261',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ( v1_funct_2 @ sk_C_1 @ X0 @ X1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('263',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
          = k1_xboole_0 )
        | ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('265',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
          = sk_C_1 )
        | ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('267',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( v5_pre_topc @ X47 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ k1_xboole_0 ) ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ( v5_pre_topc @ X1 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('270',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ( v5_pre_topc @ X1 @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['268','269','270','271'])).

thf('273',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C_1 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['265','272'])).

thf('274',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('280',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('281',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('282',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['273','274','275','276','277','278','279','280','281'])).

thf('283',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['255','282'])).

thf('284',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('286',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('288',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('290',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['197','290'])).

thf('292',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['196','294'])).

thf('296',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['295','296'])).

thf('298',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('299',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('300',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v5_pre_topc @ X51 @ X52 @ X50 )
      | ~ ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('301',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['171','172'])).

thf('303',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['301','302','303'])).

thf('305',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ sk_C_1 )
        | ( sk_C_1
          = ( u1_struct_0 @ sk_A ) )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 )
        | ~ ( v5_pre_topc @ k1_xboole_0 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        | ~ ( l1_pre_topc @ sk_B_1 )
        | ~ ( v2_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['298','304'])).

thf('306',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('307',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('308',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('309',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('310',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('311',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1
          = ( u1_struct_0 @ sk_A ) )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( v5_pre_topc @ sk_C_1 @ X0 @ sk_B_1 )
        | ~ ( v5_pre_topc @ sk_C_1 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['305','306','307','308','309','310','311','312'])).

thf('314',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['297','313'])).

thf('315',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( ( sk_C_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['314','315','316','317'])).

thf('319',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('321',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['301','302','303'])).

thf('323',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
        | ( v5_pre_topc @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( v5_pre_topc @ k1_xboole_0 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('325',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('326',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('327',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('328',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['327'])).

thf('329',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('330',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('332',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['326','332'])).

thf('334',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_funct_2 @ ( sk_C @ X36 @ X37 ) @ X37 @ X36 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('335',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['333','334'])).

thf('336',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ sk_C_1 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['325','335'])).

thf('337',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('338',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('339',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('342',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('343',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('344',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('345',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('346',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ sk_C_1 @ sk_A @ X0 )
        | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['323','324','338','339','340','341','342','343','344','345'])).

thf('347',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['195','346'])).

thf('348',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['347','348','349'])).

thf('351',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('352',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('353',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('354',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('355',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('356',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('357',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('358',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['355','358'])).

thf('360',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','83','84'])).

thf('361',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['359','360'])).

thf('362',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['354','362'])).

thf('364',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['363','364','365'])).

thf('367',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['353','366'])).

thf('368',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['367','368'])).

thf('370',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['154'])).

thf('371',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['369','370'])).

thf('372',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['371'])).

thf('373',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('374',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('375',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('376',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['374','375'])).

thf('377',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('378',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['376','377'])).

thf('379',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('380',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['378','379'])).

thf('381',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['352','380'])).

thf('382',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('383',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('384',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['333','334'])).

thf('385',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ sk_C_1 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['383','384'])).

thf('386',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('387',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['385','386'])).

thf('388',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('389',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('390',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('391',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['381','382','387','388','389','390'])).

thf('392',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('393',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('394',plain,
    ( ( ( v2_pre_topc @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['392','393'])).

thf('395',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['394','395','396'])).

thf('398',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('400',plain,
    ( ( ( l1_pre_topc @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['398','399'])).

thf('401',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['400','401'])).

thf('403',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['391','397','402'])).

thf('404',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('405',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ sk_C_1 @ sk_A @ X0 )
        | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['323','324','338','339','340','341','342','343','344','345'])).

thf('406',plain,
    ( ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['404','405'])).

thf('407',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('408',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('409',plain,
    ( ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['406','407','408'])).

thf('410',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('411',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['409','410'])).

thf('412',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['403','411'])).

thf('413',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('414',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['97','101','412','413'])).

thf('415',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['88','414'])).

thf('416',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('417',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('418',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','13','14','15'])).

thf('419',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('421',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['419','420'])).

thf('422',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['416','421'])).

thf('423',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','83','84'])).

thf('424',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['422','423'])).

thf('425',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['424'])).

thf('426',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['415','425'])).

thf('427',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','427'])).

thf('429',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['428','429'])).

thf('431',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('432',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('433',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['100'])).

thf('434',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['432','433'])).

thf('435',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['97','101','412','434'])).

thf('436',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['431','435'])).

thf('437',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['430','436'])).

thf('438',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','437'])).

thf('439',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('441',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('442',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['17','441'])).

thf('443',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['16','442'])).

thf('444',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('445',plain,(
    ! [X45: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('446',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('447',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['97','101','412','413'])).

thf('448',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['446','447'])).

thf('449',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('450',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('451',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('452',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) @ X46 )
      | ~ ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) ) ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('453',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['451','452'])).

thf('454',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['171','172'])).

thf('455',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('456',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['453','454','455'])).

thf('457',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['450','456'])).

thf('458',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('459',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('460',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['457','458','459','460'])).

thf('462',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['449','461'])).

thf('463',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('464',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['462','463'])).

thf('465',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['464'])).

thf('466',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('467',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('468',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C_1 @ X0 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['465','466','467'])).

thf('469',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['237','240','243'])).

thf('470',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('471',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('472',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['469','470','471'])).

thf('473',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C_1 @ X0 @ sk_B_1 )
      | ( sk_C_1
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['468','472'])).

thf('474',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['448','473'])).

thf('475',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['474','475','476'])).

thf('478',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('479',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('480',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['478','479'])).

thf('481',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['469','470','471'])).

thf('482',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C_1 )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['480','481'])).

thf('483',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('484',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ~ ( v5_pre_topc @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('485',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['483','484'])).

thf('486',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('487',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('488',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('489',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('490',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['485','486','487','488','489'])).

thf('491',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['17','441'])).

thf('492',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['490','491'])).

thf('493',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_C_1 )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['482','492'])).

thf('494',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('495',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('496',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('497',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['494','495','496'])).

thf('498',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['493','497'])).

thf('499',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['477','498'])).

thf('500',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['499'])).

thf('501',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['445','500'])).

thf('502',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('503',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('504',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['501','502','503'])).

thf('505',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['431','435'])).

thf('506',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['504','505'])).

thf('507',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['444','506'])).

thf('508',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('510',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('511',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['333','334'])).

thf('512',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('513',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('514',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['511','512','513'])).

thf('515',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['443','509','510','514'])).

thf('516',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['446','447'])).

thf('517',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('518',plain,(
    ! [X36: $i,X37: $i] :
      ( m1_subset_1 @ ( sk_C @ X36 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('519',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v5_pre_topc @ X51 @ X52 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) )
      | ~ ( v5_pre_topc @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X50 ) @ ( u1_pre_topc @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('520',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ X1 @ X0 )
      | ( v5_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['518','519'])).

thf('521',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_funct_1 @ ( sk_C @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('522',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_funct_2 @ ( sk_C @ X36 @ X37 ) @ X37 @ X36 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('523',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v5_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ X1 @ X0 )
      | ( v5_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['520','521','522'])).

thf('524',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['517','523'])).

thf('525',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('526',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['326','332'])).

thf('527',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('528',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('529',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['526','527','528'])).

thf('530',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['327'])).

thf('531',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('532',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('533',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ sk_C_1 @ X5 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['530','531','532'])).

thf('534',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['17','441'])).

thf('535',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('536',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('537',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('538',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['526','527','528'])).

thf('539',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('540',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['511','512','513'])).

thf('541',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('542',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['526','527','528'])).

thf('543',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('544',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['526','527','528'])).

thf('545',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['524','525','529','533','534','535','536','537','538','539','540','541','542','543','544'])).

thf('546',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['516','545'])).

thf('547',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('548',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('549',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['546','547','548'])).

thf('550',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['515','549'])).

thf('551',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['431','435'])).

thf('552',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['507','508'])).

thf('553',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ sk_C_1 @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['551','552'])).

thf('554',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['550','553'])).

thf('555',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','554'])).

thf('556',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('557',plain,(
    ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['555','556'])).

thf('558',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','557'])).

thf('559',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('560',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('561',plain,(
    $false ),
    inference(demod,[status(thm)],['558','559','560'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AWh9gI8Qwn
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:54:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.38/4.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.38/4.64  % Solved by: fo/fo7.sh
% 4.38/4.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.38/4.64  % done 4142 iterations in 4.187s
% 4.38/4.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.38/4.64  % SZS output start Refutation
% 4.38/4.64  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 4.38/4.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.38/4.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.38/4.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.38/4.64  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.38/4.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.38/4.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.38/4.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.38/4.64  thf(sk_A_type, type, sk_A: $i).
% 4.38/4.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.38/4.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.38/4.64  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 4.38/4.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.38/4.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.38/4.64  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 4.38/4.64  thf(sk_B_type, type, sk_B: $i > $i).
% 4.38/4.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.38/4.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.38/4.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.38/4.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.38/4.64  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 4.38/4.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.38/4.64  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 4.38/4.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.38/4.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.38/4.64  thf(sk_D_type, type, sk_D: $i).
% 4.38/4.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.38/4.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.38/4.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.38/4.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.38/4.64  thf(fc6_pre_topc, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.38/4.64       ( ( v1_pre_topc @
% 4.38/4.64           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 4.38/4.64         ( v2_pre_topc @
% 4.38/4.64           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 4.38/4.64  thf('0', plain,
% 4.38/4.64      (![X45 : $i]:
% 4.38/4.64         ((v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.64          | ~ (l1_pre_topc @ X45)
% 4.38/4.64          | ~ (v2_pre_topc @ X45))),
% 4.38/4.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.64  thf(dt_u1_pre_topc, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ( l1_pre_topc @ A ) =>
% 4.38/4.64       ( m1_subset_1 @
% 4.38/4.64         ( u1_pre_topc @ A ) @ 
% 4.38/4.64         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 4.38/4.64  thf('1', plain,
% 4.38/4.64      (![X44 : $i]:
% 4.38/4.64         ((m1_subset_1 @ (u1_pre_topc @ X44) @ 
% 4.38/4.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44))))
% 4.38/4.64          | ~ (l1_pre_topc @ X44))),
% 4.38/4.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.38/4.64  thf(dt_g1_pre_topc, axiom,
% 4.38/4.64    (![A:$i,B:$i]:
% 4.38/4.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.38/4.64       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 4.38/4.64         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 4.38/4.64  thf('2', plain,
% 4.38/4.64      (![X42 : $i, X43 : $i]:
% 4.38/4.64         ((l1_pre_topc @ (g1_pre_topc @ X42 @ X43))
% 4.38/4.64          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X42))))),
% 4.38/4.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 4.38/4.64  thf('3', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (l1_pre_topc @ X0)
% 4.38/4.64          | (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.64  thf(t64_pre_topc, conjecture,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.38/4.64       ( ![B:$i]:
% 4.38/4.64         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.38/4.64           ( ![C:$i]:
% 4.38/4.64             ( ( ( v1_funct_1 @ C ) & 
% 4.38/4.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.38/4.64                 ( m1_subset_1 @
% 4.38/4.64                   C @ 
% 4.38/4.64                   ( k1_zfmisc_1 @
% 4.38/4.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.38/4.64               ( ![D:$i]:
% 4.38/4.64                 ( ( ( v1_funct_1 @ D ) & 
% 4.38/4.64                     ( v1_funct_2 @
% 4.38/4.64                       D @ 
% 4.38/4.64                       ( u1_struct_0 @
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 4.38/4.64                       ( u1_struct_0 @
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 4.38/4.64                     ( m1_subset_1 @
% 4.38/4.64                       D @ 
% 4.38/4.64                       ( k1_zfmisc_1 @
% 4.38/4.64                         ( k2_zfmisc_1 @
% 4.38/4.64                           ( u1_struct_0 @
% 4.38/4.64                             ( g1_pre_topc @
% 4.38/4.64                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 4.38/4.64                           ( u1_struct_0 @
% 4.38/4.64                             ( g1_pre_topc @
% 4.38/4.64                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 4.38/4.64                   ( ( ( C ) = ( D ) ) =>
% 4.38/4.64                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.38/4.64                       ( v5_pre_topc @
% 4.38/4.64                         D @ 
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.38/4.64  thf(zf_stmt_0, negated_conjecture,
% 4.38/4.64    (~( ![A:$i]:
% 4.38/4.64        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.38/4.64          ( ![B:$i]:
% 4.38/4.64            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.38/4.64              ( ![C:$i]:
% 4.38/4.64                ( ( ( v1_funct_1 @ C ) & 
% 4.38/4.64                    ( v1_funct_2 @
% 4.38/4.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.38/4.64                    ( m1_subset_1 @
% 4.38/4.64                      C @ 
% 4.38/4.64                      ( k1_zfmisc_1 @
% 4.38/4.64                        ( k2_zfmisc_1 @
% 4.38/4.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.38/4.64                  ( ![D:$i]:
% 4.38/4.64                    ( ( ( v1_funct_1 @ D ) & 
% 4.38/4.64                        ( v1_funct_2 @
% 4.38/4.64                          D @ 
% 4.38/4.64                          ( u1_struct_0 @
% 4.38/4.64                            ( g1_pre_topc @
% 4.38/4.64                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 4.38/4.64                          ( u1_struct_0 @
% 4.38/4.64                            ( g1_pre_topc @
% 4.38/4.64                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 4.38/4.64                        ( m1_subset_1 @
% 4.38/4.64                          D @ 
% 4.38/4.64                          ( k1_zfmisc_1 @
% 4.38/4.64                            ( k2_zfmisc_1 @
% 4.38/4.64                              ( u1_struct_0 @
% 4.38/4.64                                ( g1_pre_topc @
% 4.38/4.64                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 4.38/4.64                              ( u1_struct_0 @
% 4.38/4.64                                ( g1_pre_topc @
% 4.38/4.64                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 4.38/4.64                      ( ( ( C ) = ( D ) ) =>
% 4.38/4.64                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.38/4.64                          ( v5_pre_topc @
% 4.38/4.64                            D @ 
% 4.38/4.64                            ( g1_pre_topc @
% 4.38/4.64                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 4.38/4.64                            ( g1_pre_topc @
% 4.38/4.64                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 4.38/4.64    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 4.38/4.64  thf('4', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_D @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('5', plain, (((sk_C_1) = (sk_D))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('6', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('demod', [status(thm)], ['4', '5'])).
% 4.38/4.64  thf(t62_pre_topc, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.38/4.64       ( ![B:$i]:
% 4.38/4.64         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.38/4.64           ( ![C:$i]:
% 4.38/4.64             ( ( ( v1_funct_1 @ C ) & 
% 4.38/4.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.38/4.64                 ( m1_subset_1 @
% 4.38/4.64                   C @ 
% 4.38/4.64                   ( k1_zfmisc_1 @
% 4.38/4.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.38/4.64               ( ![D:$i]:
% 4.38/4.64                 ( ( ( v1_funct_1 @ D ) & 
% 4.38/4.64                     ( v1_funct_2 @
% 4.38/4.64                       D @ 
% 4.38/4.64                       ( u1_struct_0 @
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 4.38/4.64                       ( u1_struct_0 @ B ) ) & 
% 4.38/4.64                     ( m1_subset_1 @
% 4.38/4.64                       D @ 
% 4.38/4.64                       ( k1_zfmisc_1 @
% 4.38/4.64                         ( k2_zfmisc_1 @
% 4.38/4.64                           ( u1_struct_0 @
% 4.38/4.64                             ( g1_pre_topc @
% 4.38/4.64                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 4.38/4.64                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.38/4.64                   ( ( ( C ) = ( D ) ) =>
% 4.38/4.64                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.38/4.64                       ( v5_pre_topc @
% 4.38/4.64                         D @ 
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 4.38/4.64                         B ) ) ) ) ) ) ) ) ) ))).
% 4.38/4.64  thf('7', plain,
% 4.38/4.64      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X46)
% 4.38/4.64          | ~ (l1_pre_topc @ X46)
% 4.38/4.64          | ~ (v1_funct_1 @ X47)
% 4.38/4.64          | ~ (v1_funct_2 @ X47 @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64               (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64                 (u1_struct_0 @ X46))))
% 4.38/4.64          | ~ (v5_pre_topc @ X49 @ X48 @ X46)
% 4.38/4.64          | (v5_pre_topc @ X47 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48)) @ X46)
% 4.38/4.64          | ((X49) != (X47))
% 4.38/4.64          | ~ (m1_subset_1 @ X49 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 4.38/4.64          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (v1_funct_1 @ X49)
% 4.38/4.64          | ~ (l1_pre_topc @ X48)
% 4.38/4.64          | ~ (v2_pre_topc @ X48))),
% 4.38/4.64      inference('cnf', [status(esa)], [t62_pre_topc])).
% 4.38/4.64  thf('8', plain,
% 4.38/4.64      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X48)
% 4.38/4.64          | ~ (l1_pre_topc @ X48)
% 4.38/4.64          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 4.38/4.64          | (v5_pre_topc @ X47 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48)) @ X46)
% 4.38/4.64          | ~ (v5_pre_topc @ X47 @ X48 @ X46)
% 4.38/4.64          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64                 (u1_struct_0 @ X46))))
% 4.38/4.64          | ~ (v1_funct_2 @ X47 @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64               (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (v1_funct_1 @ X47)
% 4.38/4.64          | ~ (l1_pre_topc @ X46)
% 4.38/4.64          | ~ (v2_pre_topc @ X46))),
% 4.38/4.64      inference('simplify', [status(thm)], ['7'])).
% 4.38/4.64  thf('9', plain,
% 4.38/4.64      ((~ (v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (l1_pre_topc @ sk_A)
% 4.38/4.64        | ~ (v2_pre_topc @ sk_A))),
% 4.38/4.64      inference('sup-', [status(thm)], ['6', '8'])).
% 4.38/4.64  thf('10', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('11', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_D @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('12', plain, (((sk_C_1) = (sk_D))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('13', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['11', '12'])).
% 4.38/4.64  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('16', plain,
% 4.38/4.64      ((~ (v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['9', '10', '13', '14', '15'])).
% 4.38/4.64  thf(t4_subset_1, axiom,
% 4.38/4.64    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.38/4.64  thf('17', plain,
% 4.38/4.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.64  thf('18', plain,
% 4.38/4.64      (![X45 : $i]:
% 4.38/4.64         ((v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.64          | ~ (l1_pre_topc @ X45)
% 4.38/4.64          | ~ (v2_pre_topc @ X45))),
% 4.38/4.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.64  thf('19', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (l1_pre_topc @ X0)
% 4.38/4.64          | (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.64  thf('20', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_D @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('21', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.64         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.64      inference('split', [status(esa)], ['20'])).
% 4.38/4.64  thf(t29_mcart_1, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.38/4.64          ( ![B:$i]:
% 4.38/4.64            ( ~( ( r2_hidden @ B @ A ) & 
% 4.38/4.64                 ( ![C:$i,D:$i,E:$i]:
% 4.38/4.64                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 4.38/4.64                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 4.38/4.64  thf('22', plain,
% 4.38/4.64      (![X25 : $i]:
% 4.38/4.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 4.38/4.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 4.38/4.64  thf('23', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf(t132_funct_2, axiom,
% 4.38/4.64    (![A:$i,B:$i,C:$i]:
% 4.38/4.64     ( ( ( v1_funct_1 @ C ) & 
% 4.38/4.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.38/4.64       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.38/4.64           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.38/4.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.38/4.64           ( v1_partfun1 @ C @ A ) ) ) ))).
% 4.38/4.64  thf('24', plain,
% 4.38/4.64      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.38/4.64         (((X39) = (k1_xboole_0))
% 4.38/4.64          | ~ (v1_funct_1 @ X40)
% 4.38/4.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 4.38/4.64          | (v1_partfun1 @ X40 @ X41)
% 4.38/4.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 4.38/4.64          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 4.38/4.64          | ~ (v1_funct_1 @ X40))),
% 4.38/4.64      inference('cnf', [status(esa)], [t132_funct_2])).
% 4.38/4.64  thf('25', plain,
% 4.38/4.64      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.38/4.64         (~ (v1_funct_2 @ X40 @ X41 @ X39)
% 4.38/4.64          | (v1_partfun1 @ X40 @ X41)
% 4.38/4.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 4.38/4.64          | ~ (v1_funct_1 @ X40)
% 4.38/4.64          | ((X39) = (k1_xboole_0)))),
% 4.38/4.64      inference('simplify', [status(thm)], ['24'])).
% 4.38/4.64  thf('26', plain,
% 4.38/4.64      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ sk_B_1)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['23', '25'])).
% 4.38/4.64  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('28', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('29', plain,
% 4.38/4.64      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('demod', [status(thm)], ['26', '27', '28'])).
% 4.38/4.64  thf(d4_partfun1, axiom,
% 4.38/4.64    (![A:$i,B:$i]:
% 4.38/4.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.38/4.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 4.38/4.64  thf('30', plain,
% 4.38/4.64      (![X32 : $i, X33 : $i]:
% 4.38/4.64         (~ (v1_partfun1 @ X33 @ X32)
% 4.38/4.64          | ((k1_relat_1 @ X33) = (X32))
% 4.38/4.64          | ~ (v4_relat_1 @ X33 @ X32)
% 4.38/4.64          | ~ (v1_relat_1 @ X33))),
% 4.38/4.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.38/4.64  thf('31', plain,
% 4.38/4.64      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v1_relat_1 @ sk_C_1)
% 4.38/4.64        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['29', '30'])).
% 4.38/4.64  thf('32', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf(cc1_relset_1, axiom,
% 4.38/4.64    (![A:$i,B:$i,C:$i]:
% 4.38/4.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.38/4.64       ( v1_relat_1 @ C ) ))).
% 4.38/4.64  thf('33', plain,
% 4.38/4.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.38/4.64         ((v1_relat_1 @ X14)
% 4.38/4.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.38/4.64  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 4.38/4.64      inference('sup-', [status(thm)], ['32', '33'])).
% 4.38/4.64  thf('35', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf(cc2_relset_1, axiom,
% 4.38/4.64    (![A:$i,B:$i,C:$i]:
% 4.38/4.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.38/4.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.38/4.64  thf('36', plain,
% 4.38/4.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.38/4.64         ((v4_relat_1 @ X17 @ X18)
% 4.38/4.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.38/4.64  thf('37', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 4.38/4.64      inference('sup-', [status(thm)], ['35', '36'])).
% 4.38/4.64  thf('38', plain,
% 4.38/4.64      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('demod', [status(thm)], ['31', '34', '37'])).
% 4.38/4.64  thf('39', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf(t5_subset, axiom,
% 4.38/4.64    (![A:$i,B:$i,C:$i]:
% 4.38/4.64     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.38/4.64          ( v1_xboole_0 @ C ) ) ))).
% 4.38/4.64  thf('40', plain,
% 4.38/4.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.38/4.64         (~ (r2_hidden @ X10 @ X11)
% 4.38/4.64          | ~ (v1_xboole_0 @ X12)
% 4.38/4.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 4.38/4.64      inference('cnf', [status(esa)], [t5_subset])).
% 4.38/4.64  thf('41', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (v1_xboole_0 @ 
% 4.38/4.64             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 4.38/4.64          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.38/4.64      inference('sup-', [status(thm)], ['39', '40'])).
% 4.38/4.64  thf('42', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 4.38/4.64          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.64          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.38/4.64      inference('sup-', [status(thm)], ['38', '41'])).
% 4.38/4.64  thf(t113_zfmisc_1, axiom,
% 4.38/4.64    (![A:$i,B:$i]:
% 4.38/4.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.38/4.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.38/4.64  thf('43', plain,
% 4.38/4.64      (![X4 : $i, X5 : $i]:
% 4.38/4.64         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 4.38/4.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.38/4.64  thf('44', plain,
% 4.38/4.64      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.64      inference('simplify', [status(thm)], ['43'])).
% 4.38/4.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.38/4.64  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.38/4.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.38/4.64  thf('46', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.64          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.38/4.64      inference('demod', [status(thm)], ['42', '44', '45'])).
% 4.38/4.64  thf('47', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.64  thf(d10_xboole_0, axiom,
% 4.38/4.64    (![A:$i,B:$i]:
% 4.38/4.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.38/4.64  thf('48', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.38/4.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.38/4.64  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.38/4.64      inference('simplify', [status(thm)], ['48'])).
% 4.38/4.64  thf('50', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('demod', [status(thm)], ['4', '5'])).
% 4.38/4.64  thf(t13_relset_1, axiom,
% 4.38/4.64    (![A:$i,B:$i,C:$i,D:$i]:
% 4.38/4.64     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 4.38/4.64       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 4.38/4.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 4.38/4.64  thf('51', plain,
% 4.38/4.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.38/4.64         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 4.38/4.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 4.38/4.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 4.38/4.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 4.38/4.64  thf('52', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64           (k1_zfmisc_1 @ 
% 4.38/4.64            (k2_zfmisc_1 @ X0 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 4.38/4.64      inference('sup-', [status(thm)], ['50', '51'])).
% 4.38/4.64  thf('53', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['49', '52'])).
% 4.38/4.64  thf('54', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.64  thf(t63_pre_topc, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.38/4.64       ( ![B:$i]:
% 4.38/4.64         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 4.38/4.64           ( ![C:$i]:
% 4.38/4.64             ( ( ( v1_funct_1 @ C ) & 
% 4.38/4.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.38/4.64                 ( m1_subset_1 @
% 4.38/4.64                   C @ 
% 4.38/4.64                   ( k1_zfmisc_1 @
% 4.38/4.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.38/4.64               ( ![D:$i]:
% 4.38/4.64                 ( ( ( v1_funct_1 @ D ) & 
% 4.38/4.64                     ( v1_funct_2 @
% 4.38/4.64                       D @ ( u1_struct_0 @ A ) @ 
% 4.38/4.64                       ( u1_struct_0 @
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 4.38/4.64                     ( m1_subset_1 @
% 4.38/4.64                       D @ 
% 4.38/4.64                       ( k1_zfmisc_1 @
% 4.38/4.64                         ( k2_zfmisc_1 @
% 4.38/4.64                           ( u1_struct_0 @ A ) @ 
% 4.38/4.64                           ( u1_struct_0 @
% 4.38/4.64                             ( g1_pre_topc @
% 4.38/4.64                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 4.38/4.64                   ( ( ( C ) = ( D ) ) =>
% 4.38/4.64                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.38/4.64                       ( v5_pre_topc @
% 4.38/4.64                         D @ A @ 
% 4.38/4.64                         ( g1_pre_topc @
% 4.38/4.64                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.38/4.64  thf('55', plain,
% 4.38/4.64      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X50)
% 4.38/4.64          | ~ (l1_pre_topc @ X50)
% 4.38/4.64          | ~ (v1_funct_1 @ X51)
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.64          | ~ (v5_pre_topc @ X53 @ X52 @ X50)
% 4.38/4.64          | (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.64          | ((X53) != (X51))
% 4.38/4.64          | ~ (m1_subset_1 @ X53 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.64          | ~ (v1_funct_2 @ X53 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.64          | ~ (v1_funct_1 @ X53)
% 4.38/4.64          | ~ (l1_pre_topc @ X52)
% 4.38/4.64          | ~ (v2_pre_topc @ X52))),
% 4.38/4.64      inference('cnf', [status(esa)], [t63_pre_topc])).
% 4.38/4.64  thf('56', plain,
% 4.38/4.64      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X52)
% 4.38/4.64          | ~ (l1_pre_topc @ X52)
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.64          | (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.64          | ~ (v5_pre_topc @ X51 @ X52 @ X50)
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.64          | ~ (v1_funct_1 @ X51)
% 4.38/4.64          | ~ (l1_pre_topc @ X50)
% 4.38/4.64          | ~ (v2_pre_topc @ X50))),
% 4.38/4.64      inference('simplify', [status(thm)], ['55'])).
% 4.38/4.64  thf('57', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         (~ (m1_subset_1 @ X1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 4.38/4.64          | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64          | ~ (v2_pre_topc @ X0)
% 4.38/4.64          | ~ (l1_pre_topc @ X0)
% 4.38/4.64          | ~ (v1_funct_1 @ X1)
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.64          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 4.38/4.64          | (v5_pre_topc @ X1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.64          | ~ (m1_subset_1 @ X1 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 4.38/4.64          | ~ (l1_pre_topc @ sk_A)
% 4.38/4.64          | ~ (v2_pre_topc @ sk_A))),
% 4.38/4.64      inference('sup-', [status(thm)], ['54', '56'])).
% 4.38/4.64  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('60', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         (~ (m1_subset_1 @ X1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 4.38/4.64          | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64          | ~ (v2_pre_topc @ X0)
% 4.38/4.64          | ~ (l1_pre_topc @ X0)
% 4.38/4.64          | ~ (v1_funct_1 @ X1)
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.64          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 4.38/4.64          | (v5_pre_topc @ X1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.64          | ~ (m1_subset_1 @ X1 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0)))),
% 4.38/4.64      inference('demod', [status(thm)], ['57', '58', '59'])).
% 4.38/4.64  thf('61', plain,
% 4.38/4.64      ((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64        | ~ (v2_pre_topc @ sk_B_1)
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['53', '60'])).
% 4.38/4.64  thf('62', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('63', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('65', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('66', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('67', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.64      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 4.38/4.64  thf('68', plain,
% 4.38/4.64      ((~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64           (u1_struct_0 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['47', '67'])).
% 4.38/4.64  thf('69', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['49', '52'])).
% 4.38/4.64  thf(cc1_funct_2, axiom,
% 4.38/4.64    (![A:$i,B:$i,C:$i]:
% 4.38/4.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.38/4.64       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 4.38/4.64         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 4.38/4.64  thf('70', plain,
% 4.38/4.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.38/4.64         (~ (v1_funct_1 @ X29)
% 4.38/4.64          | ~ (v1_partfun1 @ X29 @ X30)
% 4.38/4.64          | (v1_funct_2 @ X29 @ X30 @ X31)
% 4.38/4.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc1_funct_2])).
% 4.38/4.64  thf('71', plain,
% 4.38/4.64      (((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64         (u1_struct_0 @ 
% 4.38/4.64          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (v1_partfun1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1))),
% 4.38/4.64      inference('sup-', [status(thm)], ['69', '70'])).
% 4.38/4.64  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.38/4.64      inference('simplify', [status(thm)], ['48'])).
% 4.38/4.64  thf('73', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('74', plain,
% 4.38/4.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.38/4.64         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 4.38/4.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 4.38/4.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 4.38/4.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 4.38/4.64  thf('75', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B_1))))
% 4.38/4.64          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 4.38/4.64      inference('sup-', [status(thm)], ['73', '74'])).
% 4.38/4.64  thf('76', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['72', '75'])).
% 4.38/4.64  thf('77', plain,
% 4.38/4.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.38/4.64         ((v4_relat_1 @ X17 @ X18)
% 4.38/4.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.38/4.64  thf('78', plain, ((v4_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))),
% 4.38/4.64      inference('sup-', [status(thm)], ['76', '77'])).
% 4.38/4.64  thf('79', plain,
% 4.38/4.64      (![X32 : $i, X33 : $i]:
% 4.38/4.64         (((k1_relat_1 @ X33) != (X32))
% 4.38/4.64          | (v1_partfun1 @ X33 @ X32)
% 4.38/4.64          | ~ (v4_relat_1 @ X33 @ X32)
% 4.38/4.64          | ~ (v1_relat_1 @ X33))),
% 4.38/4.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.38/4.64  thf('80', plain,
% 4.38/4.64      (![X33 : $i]:
% 4.38/4.64         (~ (v1_relat_1 @ X33)
% 4.38/4.64          | ~ (v4_relat_1 @ X33 @ (k1_relat_1 @ X33))
% 4.38/4.64          | (v1_partfun1 @ X33 @ (k1_relat_1 @ X33)))),
% 4.38/4.64      inference('simplify', [status(thm)], ['79'])).
% 4.38/4.64  thf('81', plain,
% 4.38/4.64      (((v1_partfun1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 4.38/4.64        | ~ (v1_relat_1 @ sk_C_1))),
% 4.38/4.64      inference('sup-', [status(thm)], ['78', '80'])).
% 4.38/4.64  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 4.38/4.64      inference('sup-', [status(thm)], ['32', '33'])).
% 4.38/4.64  thf('83', plain, ((v1_partfun1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))),
% 4.38/4.64      inference('demod', [status(thm)], ['81', '82'])).
% 4.38/4.64  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('85', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['71', '83', '84'])).
% 4.38/4.64  thf('86', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['68', '85'])).
% 4.38/4.64  thf('87', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.64      inference('simplify', [status(thm)], ['86'])).
% 4.38/4.64  thf('88', plain,
% 4.38/4.64      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['21', '87'])).
% 4.38/4.64  thf('89', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_D @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('90', plain, (((sk_C_1) = (sk_D))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('91', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('demod', [status(thm)], ['89', '90'])).
% 4.38/4.64  thf('92', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('split', [status(esa)], ['91'])).
% 4.38/4.64  thf('93', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_D @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('94', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_D @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (~
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('split', [status(esa)], ['93'])).
% 4.38/4.64  thf('95', plain, (((sk_C_1) = (sk_D))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('96', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (~
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['94', '95'])).
% 4.38/4.64  thf('97', plain,
% 4.38/4.64      (~
% 4.38/4.64       ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 4.38/4.64       ((v5_pre_topc @ sk_D @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['92', '96'])).
% 4.38/4.64  thf('98', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_D @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('99', plain, (((sk_C_1) = (sk_D))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('100', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('demod', [status(thm)], ['98', '99'])).
% 4.38/4.64  thf('101', plain,
% 4.38/4.64      (~
% 4.38/4.64       ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 4.38/4.64       ~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('split', [status(esa)], ['100'])).
% 4.38/4.64  thf('102', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (l1_pre_topc @ X0)
% 4.38/4.64          | (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.64  thf('103', plain,
% 4.38/4.64      (![X45 : $i]:
% 4.38/4.64         ((v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.64          | ~ (l1_pre_topc @ X45)
% 4.38/4.64          | ~ (v2_pre_topc @ X45))),
% 4.38/4.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.64  thf('104', plain,
% 4.38/4.64      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('demod', [status(thm)], ['26', '27', '28'])).
% 4.38/4.64  thf('105', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (l1_pre_topc @ X0)
% 4.38/4.64          | (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.64  thf('106', plain,
% 4.38/4.64      (![X45 : $i]:
% 4.38/4.64         ((v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.64          | ~ (l1_pre_topc @ X45)
% 4.38/4.64          | ~ (v2_pre_topc @ X45))),
% 4.38/4.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.64  thf('107', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.64  thf('108', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_D @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('split', [status(esa)], ['20'])).
% 4.38/4.64  thf('109', plain, (((sk_C_1) = (sk_D))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('110', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['108', '109'])).
% 4.38/4.64  thf('111', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.64  thf('112', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('demod', [status(thm)], ['4', '5'])).
% 4.38/4.64  thf('113', plain,
% 4.38/4.64      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X46)
% 4.38/4.64          | ~ (l1_pre_topc @ X46)
% 4.38/4.64          | ~ (v1_funct_1 @ X47)
% 4.38/4.64          | ~ (v1_funct_2 @ X47 @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64               (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64                 (u1_struct_0 @ X46))))
% 4.38/4.64          | ~ (v5_pre_topc @ X47 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48)) @ X46)
% 4.38/4.64          | (v5_pre_topc @ X49 @ X48 @ X46)
% 4.38/4.64          | ((X49) != (X47))
% 4.38/4.64          | ~ (m1_subset_1 @ X49 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 4.38/4.64          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (v1_funct_1 @ X49)
% 4.38/4.64          | ~ (l1_pre_topc @ X48)
% 4.38/4.64          | ~ (v2_pre_topc @ X48))),
% 4.38/4.64      inference('cnf', [status(esa)], [t62_pre_topc])).
% 4.38/4.64  thf('114', plain,
% 4.38/4.64      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X48)
% 4.38/4.64          | ~ (l1_pre_topc @ X48)
% 4.38/4.64          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 4.38/4.64          | (v5_pre_topc @ X47 @ X48 @ X46)
% 4.38/4.64          | ~ (v5_pre_topc @ X47 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48)) @ X46)
% 4.38/4.64          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64                 (u1_struct_0 @ X46))))
% 4.38/4.64          | ~ (v1_funct_2 @ X47 @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.64               (u1_struct_0 @ X46))
% 4.38/4.64          | ~ (v1_funct_1 @ X47)
% 4.38/4.64          | ~ (l1_pre_topc @ X46)
% 4.38/4.64          | ~ (v2_pre_topc @ X46))),
% 4.38/4.64      inference('simplify', [status(thm)], ['113'])).
% 4.38/4.64  thf('115', plain,
% 4.38/4.64      ((~ (v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (l1_pre_topc @ sk_A)
% 4.38/4.64        | ~ (v2_pre_topc @ sk_A))),
% 4.38/4.64      inference('sup-', [status(thm)], ['112', '114'])).
% 4.38/4.64  thf('116', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('117', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['11', '12'])).
% 4.38/4.64  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('120', plain,
% 4.38/4.64      ((~ (v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 4.38/4.64  thf('121', plain,
% 4.38/4.64      ((~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64           (k1_zfmisc_1 @ 
% 4.38/4.64            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v2_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['111', '120'])).
% 4.38/4.64  thf('122', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['49', '52'])).
% 4.38/4.64  thf('123', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v2_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['121', '122'])).
% 4.38/4.64  thf('124', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64              (u1_struct_0 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['110', '123'])).
% 4.38/4.64  thf('125', plain,
% 4.38/4.64      (((~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64            (u1_struct_0 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['107', '124'])).
% 4.38/4.64  thf('126', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['71', '83', '84'])).
% 4.38/4.64  thf('127', plain,
% 4.38/4.64      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['125', '126'])).
% 4.38/4.64  thf('128', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('simplify', [status(thm)], ['127'])).
% 4.38/4.64  thf('129', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.64         | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['106', '128'])).
% 4.38/4.64  thf('130', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('131', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('132', plain,
% 4.38/4.64      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['129', '130', '131'])).
% 4.38/4.64  thf('133', plain,
% 4.38/4.64      (((~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['105', '132'])).
% 4.38/4.64  thf('134', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('135', plain,
% 4.38/4.64      ((((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['133', '134'])).
% 4.38/4.64  thf('136', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.64  thf('137', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['49', '52'])).
% 4.38/4.64  thf('138', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.64  thf('139', plain,
% 4.38/4.64      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X50)
% 4.38/4.64          | ~ (l1_pre_topc @ X50)
% 4.38/4.64          | ~ (v1_funct_1 @ X51)
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.64          | ~ (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.64          | (v5_pre_topc @ X53 @ X52 @ X50)
% 4.38/4.64          | ((X53) != (X51))
% 4.38/4.64          | ~ (m1_subset_1 @ X53 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.64          | ~ (v1_funct_2 @ X53 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.64          | ~ (v1_funct_1 @ X53)
% 4.38/4.64          | ~ (l1_pre_topc @ X52)
% 4.38/4.64          | ~ (v2_pre_topc @ X52))),
% 4.38/4.64      inference('cnf', [status(esa)], [t63_pre_topc])).
% 4.38/4.64  thf('140', plain,
% 4.38/4.64      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X52)
% 4.38/4.64          | ~ (l1_pre_topc @ X52)
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.64          | (v5_pre_topc @ X51 @ X52 @ X50)
% 4.38/4.64          | ~ (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.64          | ~ (v1_funct_1 @ X51)
% 4.38/4.64          | ~ (l1_pre_topc @ X50)
% 4.38/4.64          | ~ (v2_pre_topc @ X50))),
% 4.38/4.64      inference('simplify', [status(thm)], ['139'])).
% 4.38/4.64  thf('141', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         (~ (m1_subset_1 @ X1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 4.38/4.64          | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64          | ~ (v2_pre_topc @ X0)
% 4.38/4.64          | ~ (l1_pre_topc @ X0)
% 4.38/4.64          | ~ (v1_funct_1 @ X1)
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.64          | ~ (v5_pre_topc @ X1 @ sk_A @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.64          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 4.38/4.64          | ~ (m1_subset_1 @ X1 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 4.38/4.64          | ~ (l1_pre_topc @ sk_A)
% 4.38/4.64          | ~ (v2_pre_topc @ sk_A))),
% 4.38/4.64      inference('sup-', [status(thm)], ['138', '140'])).
% 4.38/4.64  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('144', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         (~ (m1_subset_1 @ X1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 4.38/4.64          | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64          | ~ (v2_pre_topc @ X0)
% 4.38/4.64          | ~ (l1_pre_topc @ X0)
% 4.38/4.64          | ~ (v1_funct_1 @ X1)
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.64          | ~ (v5_pre_topc @ X1 @ sk_A @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.64          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 4.38/4.64          | ~ (m1_subset_1 @ X1 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 4.38/4.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0)))),
% 4.38/4.64      inference('demod', [status(thm)], ['141', '142', '143'])).
% 4.38/4.64  thf('145', plain,
% 4.38/4.64      ((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64        | ~ (v2_pre_topc @ sk_B_1)
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['137', '144'])).
% 4.38/4.64  thf('146', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('147', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('148', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('149', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('150', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('151', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.64      inference('demod', [status(thm)],
% 4.38/4.64                ['145', '146', '147', '148', '149', '150'])).
% 4.38/4.64  thf('152', plain,
% 4.38/4.64      ((~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64           (u1_struct_0 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('sup-', [status(thm)], ['136', '151'])).
% 4.38/4.64  thf('153', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['71', '83', '84'])).
% 4.38/4.64  thf('154', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.64      inference('demod', [status(thm)], ['152', '153'])).
% 4.38/4.64  thf('155', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.64      inference('simplify', [status(thm)], ['154'])).
% 4.38/4.64  thf('156', plain,
% 4.38/4.64      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['135', '155'])).
% 4.38/4.64  thf('157', plain,
% 4.38/4.64      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1) | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('simplify', [status(thm)], ['156'])).
% 4.38/4.64  thf('158', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.64      inference('split', [status(esa)], ['93'])).
% 4.38/4.64  thf('159', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('160', plain,
% 4.38/4.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.64  thf('161', plain,
% 4.38/4.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.38/4.64         (~ (v1_funct_1 @ X29)
% 4.38/4.64          | ~ (v1_partfun1 @ X29 @ X30)
% 4.38/4.64          | (v1_funct_2 @ X29 @ X30 @ X31)
% 4.38/4.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc1_funct_2])).
% 4.38/4.64  thf('162', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.64          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 4.38/4.64          | ~ (v1_funct_1 @ k1_xboole_0))),
% 4.38/4.64      inference('sup-', [status(thm)], ['160', '161'])).
% 4.38/4.64  thf('163', plain,
% 4.38/4.64      (![X25 : $i]:
% 4.38/4.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 4.38/4.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 4.38/4.64  thf('164', plain,
% 4.38/4.64      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.64      inference('simplify', [status(thm)], ['43'])).
% 4.38/4.64  thf(rc1_funct_2, axiom,
% 4.38/4.64    (![A:$i,B:$i]:
% 4.38/4.64     ( ?[C:$i]:
% 4.38/4.64       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 4.38/4.64         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 4.38/4.64         ( v1_relat_1 @ C ) & 
% 4.38/4.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.38/4.64  thf('165', plain,
% 4.38/4.64      (![X36 : $i, X37 : $i]:
% 4.38/4.64         (m1_subset_1 @ (sk_C @ X36 @ X37) @ 
% 4.38/4.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))),
% 4.38/4.64      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.64  thf('166', plain,
% 4.38/4.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.38/4.64         (~ (r2_hidden @ X10 @ X11)
% 4.38/4.64          | ~ (v1_xboole_0 @ X12)
% 4.38/4.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 4.38/4.64      inference('cnf', [status(esa)], [t5_subset])).
% 4.38/4.64  thf('167', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.38/4.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.38/4.64          | ~ (r2_hidden @ X2 @ (sk_C @ X0 @ X1)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['165', '166'])).
% 4.38/4.64  thf('168', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.38/4.64          | ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['164', '167'])).
% 4.38/4.64  thf('169', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.38/4.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.38/4.64  thf('170', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0))),
% 4.38/4.64      inference('demod', [status(thm)], ['168', '169'])).
% 4.38/4.64  thf('171', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.38/4.64      inference('sup-', [status(thm)], ['163', '170'])).
% 4.38/4.64  thf('172', plain, (![X36 : $i, X37 : $i]: (v1_funct_1 @ (sk_C @ X36 @ X37))),
% 4.38/4.64      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.64  thf('173', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.38/4.64      inference('sup+', [status(thm)], ['171', '172'])).
% 4.38/4.64  thf('174', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.64          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 4.38/4.64      inference('demod', [status(thm)], ['162', '173'])).
% 4.38/4.64  thf('175', plain,
% 4.38/4.64      ((![X0 : $i, X1 : $i]:
% 4.38/4.64          (~ (v1_partfun1 @ sk_C_1 @ X0) | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['159', '174'])).
% 4.38/4.64  thf('176', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('177', plain,
% 4.38/4.64      ((![X0 : $i, X1 : $i]:
% 4.38/4.64          (~ (v1_partfun1 @ sk_C_1 @ X0) | (v1_funct_2 @ sk_C_1 @ X0 @ X1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['175', '176'])).
% 4.38/4.64  thf('178', plain,
% 4.38/4.64      ((![X0 : $i]:
% 4.38/4.64          (((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64           | (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['104', '177'])).
% 4.38/4.64  thf('179', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('180', plain,
% 4.38/4.64      ((![X0 : $i]:
% 4.38/4.64          (((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.64           | (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['178', '179'])).
% 4.38/4.64  thf('181', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('182', plain,
% 4.38/4.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.64  thf('183', plain,
% 4.38/4.64      ((![X0 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup+', [status(thm)], ['181', '182'])).
% 4.38/4.64  thf('184', plain,
% 4.38/4.64      ((~ (v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 4.38/4.64  thf('185', plain,
% 4.38/4.64      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64            (u1_struct_0 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['183', '184'])).
% 4.38/4.64  thf('186', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['108', '109'])).
% 4.38/4.64  thf('187', plain,
% 4.38/4.64      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.64            (u1_struct_0 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['185', '186'])).
% 4.38/4.64  thf('188', plain,
% 4.38/4.64      (((((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['180', '187'])).
% 4.38/4.64  thf('189', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.64         | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ((u1_struct_0 @ sk_B_1) = (sk_C_1))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['103', '188'])).
% 4.38/4.64  thf('190', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('191', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('192', plain,
% 4.38/4.64      ((((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64         | ((u1_struct_0 @ sk_B_1) = (sk_C_1))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['189', '190', '191'])).
% 4.38/4.64  thf('193', plain,
% 4.38/4.64      (((~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64         | ((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['102', '192'])).
% 4.38/4.64  thf('194', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('195', plain,
% 4.38/4.64      (((((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['193', '194'])).
% 4.38/4.64  thf('196', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (l1_pre_topc @ X0)
% 4.38/4.64          | (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.64  thf('197', plain,
% 4.38/4.64      (![X45 : $i]:
% 4.38/4.64         ((v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.64          | ~ (l1_pre_topc @ X45)
% 4.38/4.64          | ~ (v2_pre_topc @ X45))),
% 4.38/4.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.64  thf('198', plain,
% 4.38/4.64      (![X45 : $i]:
% 4.38/4.64         ((v2_pre_topc @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.64          | ~ (l1_pre_topc @ X45)
% 4.38/4.64          | ~ (v2_pre_topc @ X45))),
% 4.38/4.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.64  thf('199', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (l1_pre_topc @ X0)
% 4.38/4.64          | (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.64  thf('200', plain,
% 4.38/4.64      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.64        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.64      inference('demod', [status(thm)], ['31', '34', '37'])).
% 4.38/4.64  thf('201', plain,
% 4.38/4.64      ((![X0 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup+', [status(thm)], ['181', '182'])).
% 4.38/4.64  thf('202', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('demod', [status(thm)], ['4', '5'])).
% 4.38/4.64  thf('203', plain,
% 4.38/4.64      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.38/4.64         (~ (v2_pre_topc @ X52)
% 4.38/4.64          | ~ (l1_pre_topc @ X52)
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.64          | (v5_pre_topc @ X51 @ X52 @ X50)
% 4.38/4.64          | ~ (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.64          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.64               (k1_zfmisc_1 @ 
% 4.38/4.64                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64                 (u1_struct_0 @ 
% 4.38/4.64                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.64          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.64          | ~ (v1_funct_1 @ X51)
% 4.38/4.64          | ~ (l1_pre_topc @ X50)
% 4.38/4.64          | ~ (v2_pre_topc @ X50))),
% 4.38/4.64      inference('simplify', [status(thm)], ['139'])).
% 4.38/4.64  thf('204', plain,
% 4.38/4.64      ((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.64        | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64               (u1_struct_0 @ sk_B_1))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64             (u1_struct_0 @ sk_B_1))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64        | ~ (v2_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['202', '203'])).
% 4.38/4.64  thf('205', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('206', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('207', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('208', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['11', '12'])).
% 4.38/4.64  thf('209', plain,
% 4.38/4.64      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 4.38/4.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64             (k1_zfmisc_1 @ 
% 4.38/4.64              (k2_zfmisc_1 @ 
% 4.38/4.64               (u1_struct_0 @ 
% 4.38/4.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64               (u1_struct_0 @ sk_B_1))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64             (u1_struct_0 @ sk_B_1))
% 4.38/4.64        | ~ (l1_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64        | ~ (v2_pre_topc @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.64      inference('demod', [status(thm)], ['204', '205', '206', '207', '208'])).
% 4.38/4.64  thf('210', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64              (u1_struct_0 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64              (u1_struct_0 @ sk_B_1))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)
% 4.38/4.64         | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['201', '209'])).
% 4.38/4.64  thf('211', plain,
% 4.38/4.64      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.64         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['108', '109'])).
% 4.38/4.64  thf('212', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64              (u1_struct_0 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64              (u1_struct_0 @ sk_B_1))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['210', '211'])).
% 4.38/4.64  thf('213', plain,
% 4.38/4.64      (((~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64            (u1_struct_0 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64            k1_xboole_0)
% 4.38/4.64         | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['200', '212'])).
% 4.38/4.64  thf('214', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('215', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('216', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.38/4.64      inference('sup-', [status(thm)], ['163', '170'])).
% 4.38/4.64  thf('217', plain,
% 4.38/4.64      (![X36 : $i, X37 : $i]: (v1_funct_2 @ (sk_C @ X36 @ X37) @ X37 @ X36)),
% 4.38/4.64      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.64  thf('218', plain,
% 4.38/4.64      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.38/4.64      inference('sup+', [status(thm)], ['216', '217'])).
% 4.38/4.64  thf('219', plain,
% 4.38/4.64      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_C_1))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup+', [status(thm)], ['215', '218'])).
% 4.38/4.64  thf('220', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('221', plain,
% 4.38/4.64      ((![X0 : $i]: (v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['219', '220'])).
% 4.38/4.64  thf('222', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('223', plain,
% 4.38/4.64      (![X25 : $i]:
% 4.38/4.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 4.38/4.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 4.38/4.64  thf('224', plain,
% 4.38/4.64      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.64      inference('simplify', [status(thm)], ['43'])).
% 4.38/4.64  thf(t29_relset_1, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( m1_subset_1 @
% 4.38/4.64       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.38/4.64  thf('225', plain,
% 4.38/4.64      (![X24 : $i]:
% 4.38/4.64         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 4.38/4.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 4.38/4.64      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.38/4.64  thf('226', plain,
% 4.38/4.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.38/4.64         (~ (r2_hidden @ X10 @ X11)
% 4.38/4.64          | ~ (v1_xboole_0 @ X12)
% 4.38/4.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 4.38/4.64      inference('cnf', [status(esa)], [t5_subset])).
% 4.38/4.64  thf('227', plain,
% 4.38/4.64      (![X0 : $i, X1 : $i]:
% 4.38/4.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 4.38/4.64          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['225', '226'])).
% 4.38/4.64  thf('228', plain,
% 4.38/4.64      (![X0 : $i]:
% 4.38/4.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.38/4.64          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['224', '227'])).
% 4.38/4.64  thf('229', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.38/4.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.38/4.64  thf('230', plain,
% 4.38/4.64      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 4.38/4.64      inference('demod', [status(thm)], ['228', '229'])).
% 4.38/4.64  thf('231', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.64      inference('sup-', [status(thm)], ['223', '230'])).
% 4.38/4.64  thf(dt_k6_partfun1, axiom,
% 4.38/4.64    (![A:$i]:
% 4.38/4.64     ( ( m1_subset_1 @
% 4.38/4.64         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.38/4.64       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.38/4.64  thf('232', plain, (![X34 : $i]: (v1_partfun1 @ (k6_partfun1 @ X34) @ X34)),
% 4.38/4.64      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.38/4.64  thf(redefinition_k6_partfun1, axiom,
% 4.38/4.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.38/4.64  thf('233', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 4.38/4.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.38/4.64  thf('234', plain, (![X34 : $i]: (v1_partfun1 @ (k6_relat_1 @ X34) @ X34)),
% 4.38/4.64      inference('demod', [status(thm)], ['232', '233'])).
% 4.38/4.64  thf('235', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 4.38/4.64      inference('sup+', [status(thm)], ['231', '234'])).
% 4.38/4.64  thf('236', plain,
% 4.38/4.64      (![X32 : $i, X33 : $i]:
% 4.38/4.64         (~ (v1_partfun1 @ X33 @ X32)
% 4.38/4.64          | ((k1_relat_1 @ X33) = (X32))
% 4.38/4.64          | ~ (v4_relat_1 @ X33 @ X32)
% 4.38/4.64          | ~ (v1_relat_1 @ X33))),
% 4.38/4.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.38/4.64  thf('237', plain,
% 4.38/4.64      ((~ (v1_relat_1 @ k1_xboole_0)
% 4.38/4.64        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 4.38/4.64        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.38/4.64      inference('sup-', [status(thm)], ['235', '236'])).
% 4.38/4.64  thf('238', plain,
% 4.38/4.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.64  thf('239', plain,
% 4.38/4.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.38/4.64         ((v1_relat_1 @ X14)
% 4.38/4.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.38/4.64  thf('240', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.38/4.64      inference('sup-', [status(thm)], ['238', '239'])).
% 4.38/4.64  thf('241', plain,
% 4.38/4.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.64  thf('242', plain,
% 4.38/4.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.38/4.64         ((v4_relat_1 @ X17 @ X18)
% 4.38/4.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.38/4.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.38/4.64  thf('243', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 4.38/4.64      inference('sup-', [status(thm)], ['241', '242'])).
% 4.38/4.64  thf('244', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.64      inference('demod', [status(thm)], ['237', '240', '243'])).
% 4.38/4.64  thf('245', plain,
% 4.38/4.64      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup+', [status(thm)], ['222', '244'])).
% 4.38/4.64  thf('246', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.64  thf('247', plain,
% 4.38/4.64      ((((k1_relat_1 @ sk_C_1) = (sk_C_1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['245', '246'])).
% 4.38/4.64  thf('248', plain,
% 4.38/4.64      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)
% 4.38/4.64         | ~ (l1_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['213', '214', '221', '247'])).
% 4.38/4.64  thf('249', plain,
% 4.38/4.64      (((~ (l1_pre_topc @ sk_A)
% 4.38/4.64         | ~ (v2_pre_topc @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)
% 4.38/4.64         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['199', '248'])).
% 4.38/4.64  thf('250', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('251', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)
% 4.38/4.64         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['249', '250'])).
% 4.38/4.64  thf('252', plain,
% 4.38/4.64      (((~ (v2_pre_topc @ sk_A)
% 4.38/4.64         | ~ (l1_pre_topc @ sk_A)
% 4.38/4.64         | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['198', '251'])).
% 4.38/4.64  thf('253', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('254', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('255', plain,
% 4.38/4.64      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.64         | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64            sk_B_1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['252', '253', '254'])).
% 4.38/4.64  thf('256', plain,
% 4.38/4.64      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.64        (k1_zfmisc_1 @ 
% 4.38/4.64         (k2_zfmisc_1 @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64          (u1_struct_0 @ 
% 4.38/4.64           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.64      inference('demod', [status(thm)], ['4', '5'])).
% 4.38/4.64  thf('257', plain,
% 4.38/4.64      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.38/4.64         (~ (v1_funct_2 @ X40 @ X41 @ X39)
% 4.38/4.64          | (v1_partfun1 @ X40 @ X41)
% 4.38/4.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 4.38/4.64          | ~ (v1_funct_1 @ X40)
% 4.38/4.64          | ((X39) = (k1_xboole_0)))),
% 4.38/4.64      inference('simplify', [status(thm)], ['24'])).
% 4.38/4.64  thf('258', plain,
% 4.38/4.64      ((((u1_struct_0 @ 
% 4.38/4.64          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64          = (k1_xboole_0))
% 4.38/4.64        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.64        | (v1_partfun1 @ sk_C_1 @ 
% 4.38/4.64           (u1_struct_0 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 4.38/4.64        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64             (u1_struct_0 @ 
% 4.38/4.64              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['256', '257'])).
% 4.38/4.64  thf('259', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.64  thf('260', plain,
% 4.38/4.64      ((v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64        (u1_struct_0 @ 
% 4.38/4.64         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.64      inference('demod', [status(thm)], ['11', '12'])).
% 4.38/4.64  thf('261', plain,
% 4.38/4.64      ((((u1_struct_0 @ 
% 4.38/4.64          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64          = (k1_xboole_0))
% 4.38/4.64        | (v1_partfun1 @ sk_C_1 @ 
% 4.38/4.64           (u1_struct_0 @ 
% 4.38/4.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['258', '259', '260'])).
% 4.38/4.64  thf('262', plain,
% 4.38/4.64      ((![X0 : $i, X1 : $i]:
% 4.38/4.64          (~ (v1_partfun1 @ sk_C_1 @ X0) | (v1_funct_2 @ sk_C_1 @ X0 @ X1)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('demod', [status(thm)], ['175', '176'])).
% 4.38/4.64  thf('263', plain,
% 4.38/4.64      ((![X0 : $i]:
% 4.38/4.64          (((u1_struct_0 @ 
% 4.38/4.64             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.64             = (k1_xboole_0))
% 4.38/4.64           | (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.64              (u1_struct_0 @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.64              X0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.64      inference('sup-', [status(thm)], ['261', '262'])).
% 4.38/4.64  thf('264', plain,
% 4.38/4.64      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.64         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.64             ((v5_pre_topc @ sk_D @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.64               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('265', plain,
% 4.38/4.65      ((![X0 : $i]:
% 4.38/4.65          (((u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65             = (sk_C_1))
% 4.38/4.65           | (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65              X0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['263', '264'])).
% 4.38/4.65  thf('266', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['31', '34', '37'])).
% 4.38/4.65  thf('267', plain,
% 4.38/4.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X48)
% 4.38/4.65          | ~ (l1_pre_topc @ X48)
% 4.38/4.65          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 4.38/4.65          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 4.38/4.65          | (v5_pre_topc @ X47 @ X48 @ X46)
% 4.38/4.65          | ~ (v5_pre_topc @ X47 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48)) @ X46)
% 4.38/4.65          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ 
% 4.38/4.65                 (u1_struct_0 @ 
% 4.38/4.65                  (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.65                 (u1_struct_0 @ X46))))
% 4.38/4.65          | ~ (v1_funct_2 @ X47 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.65               (u1_struct_0 @ X46))
% 4.38/4.65          | ~ (v1_funct_1 @ X47)
% 4.38/4.65          | ~ (l1_pre_topc @ X46)
% 4.38/4.65          | ~ (v2_pre_topc @ X46))),
% 4.38/4.65      inference('simplify', [status(thm)], ['113'])).
% 4.38/4.65  thf('268', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (m1_subset_1 @ X1 @ 
% 4.38/4.65             (k1_zfmisc_1 @ 
% 4.38/4.65              (k2_zfmisc_1 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65               k1_xboole_0)))
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65          | ~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65          | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65          | ~ (v1_funct_1 @ X1)
% 4.38/4.65          | ~ (v1_funct_2 @ X1 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65               (u1_struct_0 @ sk_B_1))
% 4.38/4.65          | ~ (v5_pre_topc @ X1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | (v5_pre_topc @ X1 @ X0 @ sk_B_1)
% 4.38/4.65          | ~ (m1_subset_1 @ X1 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 4.38/4.65          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v2_pre_topc @ X0))),
% 4.38/4.65      inference('sup-', [status(thm)], ['266', '267'])).
% 4.38/4.65  thf('269', plain,
% 4.38/4.65      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.65      inference('simplify', [status(thm)], ['43'])).
% 4.38/4.65  thf('270', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('271', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('272', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65          | ~ (v1_funct_1 @ X1)
% 4.38/4.65          | ~ (v1_funct_2 @ X1 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65               (u1_struct_0 @ sk_B_1))
% 4.38/4.65          | ~ (v5_pre_topc @ X1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | (v5_pre_topc @ X1 @ X0 @ sk_B_1)
% 4.38/4.65          | ~ (m1_subset_1 @ X1 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 4.38/4.65          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v2_pre_topc @ X0))),
% 4.38/4.65      inference('demod', [status(thm)], ['268', '269', '270', '271'])).
% 4.38/4.65  thf('273', plain,
% 4.38/4.65      (((((u1_struct_0 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65           = (sk_C_1))
% 4.38/4.65         | ~ (v2_pre_topc @ sk_A)
% 4.38/4.65         | ~ (l1_pre_topc @ sk_A)
% 4.38/4.65         | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65              (u1_struct_0 @ sk_B_1))
% 4.38/4.65         | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65              (k1_zfmisc_1 @ 
% 4.38/4.65               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65              sk_B_1)
% 4.38/4.65         | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.65         | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['265', '272'])).
% 4.38/4.65  thf('274', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('275', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('276', plain,
% 4.38/4.65      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('277', plain,
% 4.38/4.65      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65        (k1_zfmisc_1 @ 
% 4.38/4.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('278', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('279', plain,
% 4.38/4.65      ((((k1_relat_1 @ sk_C_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['245', '246'])).
% 4.38/4.65  thf('280', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('281', plain,
% 4.38/4.65      ((![X0 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup+', [status(thm)], ['181', '182'])).
% 4.38/4.65  thf('282', plain,
% 4.38/4.65      (((((u1_struct_0 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65           = (sk_C_1))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65              sk_B_1)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)],
% 4.38/4.65                ['273', '274', '275', '276', '277', '278', '279', '280', '281'])).
% 4.38/4.65  thf('283', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ((u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65             = (sk_C_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['255', '282'])).
% 4.38/4.65  thf('284', plain,
% 4.38/4.65      (((((u1_struct_0 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65           = (sk_C_1))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('simplify', [status(thm)], ['283'])).
% 4.38/4.65  thf('285', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.65      inference('split', [status(esa)], ['93'])).
% 4.38/4.65  thf('286', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | ((u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65             = (sk_C_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['284', '285'])).
% 4.38/4.65  thf('287', plain,
% 4.38/4.65      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65            (u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['185', '186'])).
% 4.38/4.65  thf('288', plain,
% 4.38/4.65      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['286', '287'])).
% 4.38/4.65  thf('289', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['219', '220'])).
% 4.38/4.65  thf('290', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['288', '289'])).
% 4.38/4.65  thf('291', plain,
% 4.38/4.65      (((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65         | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['197', '290'])).
% 4.38/4.65  thf('292', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('293', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('294', plain,
% 4.38/4.65      ((((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['291', '292', '293'])).
% 4.38/4.65  thf('295', plain,
% 4.38/4.65      (((~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['196', '294'])).
% 4.38/4.65  thf('296', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('297', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['295', '296'])).
% 4.38/4.65  thf('298', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | ((u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65             = (sk_C_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['284', '285'])).
% 4.38/4.65  thf('299', plain,
% 4.38/4.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.65  thf('300', plain,
% 4.38/4.65      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X52)
% 4.38/4.65          | ~ (l1_pre_topc @ X52)
% 4.38/4.65          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.65          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.65          | (v5_pre_topc @ X51 @ X52 @ X50)
% 4.38/4.65          | ~ (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.65          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.65                 (u1_struct_0 @ 
% 4.38/4.65                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.65          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.65          | ~ (v1_funct_1 @ X51)
% 4.38/4.65          | ~ (l1_pre_topc @ X50)
% 4.38/4.65          | ~ (v2_pre_topc @ X50))),
% 4.38/4.65      inference('simplify', [status(thm)], ['139'])).
% 4.38/4.65  thf('301', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_1 @ k1_xboole_0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.65          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['299', '300'])).
% 4.38/4.65  thf('302', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['171', '172'])).
% 4.38/4.65  thf('303', plain,
% 4.38/4.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.65  thf('304', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('demod', [status(thm)], ['301', '302', '303'])).
% 4.38/4.65  thf('305', plain,
% 4.38/4.65      ((![X0 : $i]:
% 4.38/4.65          (~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X0) @ sk_C_1)
% 4.38/4.65           | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65           | ~ (v2_pre_topc @ X0)
% 4.38/4.65           | ~ (l1_pre_topc @ X0)
% 4.38/4.65           | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 4.38/4.65                (u1_struct_0 @ sk_B_1))
% 4.38/4.65           | (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1)
% 4.38/4.65           | ~ (v5_pre_topc @ k1_xboole_0 @ X0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65           | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65           | ~ (v2_pre_topc @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['298', '304'])).
% 4.38/4.65  thf('306', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('307', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['219', '220'])).
% 4.38/4.65  thf('308', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('309', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('310', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('311', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('312', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('313', plain,
% 4.38/4.65      ((![X0 : $i]:
% 4.38/4.65          (((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65           | ~ (v2_pre_topc @ X0)
% 4.38/4.65           | ~ (l1_pre_topc @ X0)
% 4.38/4.65           | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ X0) @ 
% 4.38/4.65                (u1_struct_0 @ sk_B_1))
% 4.38/4.65           | (v5_pre_topc @ sk_C_1 @ X0 @ sk_B_1)
% 4.38/4.65           | ~ (v5_pre_topc @ sk_C_1 @ X0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)],
% 4.38/4.65                ['305', '306', '307', '308', '309', '310', '311', '312'])).
% 4.38/4.65  thf('314', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65              (u1_struct_0 @ sk_B_1))
% 4.38/4.65         | ~ (l1_pre_topc @ sk_A)
% 4.38/4.65         | ~ (v2_pre_topc @ sk_A)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['297', '313'])).
% 4.38/4.65  thf('315', plain,
% 4.38/4.65      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('316', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('317', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('318', plain,
% 4.38/4.65      (((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['314', '315', '316', '317'])).
% 4.38/4.65  thf('319', plain,
% 4.38/4.65      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65         | ((sk_C_1) = (u1_struct_0 @ sk_A))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('simplify', [status(thm)], ['318'])).
% 4.38/4.65  thf('320', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.65      inference('split', [status(esa)], ['93'])).
% 4.38/4.65  thf('321', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['319', '320'])).
% 4.38/4.65  thf('322', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('demod', [status(thm)], ['301', '302', '303'])).
% 4.38/4.65  thf('323', plain,
% 4.38/4.65      ((![X0 : $i]:
% 4.38/4.65          (~ (v1_funct_2 @ k1_xboole_0 @ sk_C_1 @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.65           | ~ (v2_pre_topc @ sk_A)
% 4.38/4.65           | ~ (l1_pre_topc @ sk_A)
% 4.38/4.65           | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65                (u1_struct_0 @ X0))
% 4.38/4.65           | (v5_pre_topc @ k1_xboole_0 @ sk_A @ X0)
% 4.38/4.65           | ~ (v5_pre_topc @ k1_xboole_0 @ sk_A @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65           | ~ (l1_pre_topc @ X0)
% 4.38/4.65           | ~ (v2_pre_topc @ X0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['321', '322'])).
% 4.38/4.65  thf('324', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('325', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('326', plain,
% 4.38/4.65      (![X25 : $i]:
% 4.38/4.65         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 4.38/4.65      inference('cnf', [status(esa)], [t29_mcart_1])).
% 4.38/4.65  thf('327', plain,
% 4.38/4.65      (![X4 : $i, X5 : $i]:
% 4.38/4.65         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 4.38/4.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.38/4.65  thf('328', plain,
% 4.38/4.65      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 4.38/4.65      inference('simplify', [status(thm)], ['327'])).
% 4.38/4.65  thf('329', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.38/4.65         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.38/4.65          | ~ (r2_hidden @ X2 @ (sk_C @ X0 @ X1)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['165', '166'])).
% 4.38/4.65  thf('330', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.38/4.65          | ~ (r2_hidden @ X1 @ (sk_C @ X0 @ k1_xboole_0)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['328', '329'])).
% 4.38/4.65  thf('331', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.38/4.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.38/4.65  thf('332', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (sk_C @ X0 @ k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['330', '331'])).
% 4.38/4.65  thf('333', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.65      inference('sup-', [status(thm)], ['326', '332'])).
% 4.38/4.65  thf('334', plain,
% 4.38/4.65      (![X36 : $i, X37 : $i]: (v1_funct_2 @ (sk_C @ X36 @ X37) @ X37 @ X36)),
% 4.38/4.65      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.65  thf('335', plain,
% 4.38/4.65      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['333', '334'])).
% 4.38/4.65  thf('336', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ sk_C_1 @ X0))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup+', [status(thm)], ['325', '335'])).
% 4.38/4.65  thf('337', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('338', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['336', '337'])).
% 4.38/4.65  thf('339', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('340', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('341', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('342', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['319', '320'])).
% 4.38/4.65  thf('343', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['336', '337'])).
% 4.38/4.65  thf('344', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('345', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['157', '158'])).
% 4.38/4.65  thf('346', plain,
% 4.38/4.65      ((![X0 : $i]:
% 4.38/4.65          ((v5_pre_topc @ sk_C_1 @ sk_A @ X0)
% 4.38/4.65           | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65           | ~ (l1_pre_topc @ X0)
% 4.38/4.65           | ~ (v2_pre_topc @ X0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)],
% 4.38/4.65                ['323', '324', '338', '339', '340', '341', '342', '343', 
% 4.38/4.65                 '344', '345'])).
% 4.38/4.65  thf('347', plain,
% 4.38/4.65      (((((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.65         | ~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65         | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['195', '346'])).
% 4.38/4.65  thf('348', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('349', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('350', plain,
% 4.38/4.65      (((((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['347', '348', '349'])).
% 4.38/4.65  thf('351', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.65      inference('split', [status(esa)], ['93'])).
% 4.38/4.65  thf('352', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('353', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (l1_pre_topc @ X0)
% 4.38/4.65          | (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.65  thf('354', plain,
% 4.38/4.65      (![X45 : $i]:
% 4.38/4.65         ((v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.65          | ~ (l1_pre_topc @ X45)
% 4.38/4.65          | ~ (v2_pre_topc @ X45))),
% 4.38/4.65      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.65  thf('355', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.65  thf('356', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('split', [status(esa)], ['91'])).
% 4.38/4.65  thf('357', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['121', '122'])).
% 4.38/4.65  thf('358', plain,
% 4.38/4.65      (((~ (v2_pre_topc @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['356', '357'])).
% 4.38/4.65  thf('359', plain,
% 4.38/4.65      (((~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.65            (u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['355', '358'])).
% 4.38/4.65  thf('360', plain,
% 4.38/4.65      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.65        (u1_struct_0 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['71', '83', '84'])).
% 4.38/4.65  thf('361', plain,
% 4.38/4.65      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['359', '360'])).
% 4.38/4.65  thf('362', plain,
% 4.38/4.65      (((~ (v2_pre_topc @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('simplify', [status(thm)], ['361'])).
% 4.38/4.65  thf('363', plain,
% 4.38/4.65      (((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65         | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['354', '362'])).
% 4.38/4.65  thf('364', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('365', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('366', plain,
% 4.38/4.65      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['363', '364', '365'])).
% 4.38/4.65  thf('367', plain,
% 4.38/4.65      (((~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['353', '366'])).
% 4.38/4.65  thf('368', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('369', plain,
% 4.38/4.65      ((((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['367', '368'])).
% 4.38/4.65  thf('370', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('simplify', [status(thm)], ['154'])).
% 4.38/4.65  thf('371', plain,
% 4.38/4.65      (((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['369', '370'])).
% 4.38/4.65  thf('372', plain,
% 4.38/4.65      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1) | ((sk_C_1) = (k1_xboole_0))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('simplify', [status(thm)], ['371'])).
% 4.38/4.65  thf('373', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.65      inference('split', [status(esa)], ['93'])).
% 4.38/4.65  thf('374', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['372', '373'])).
% 4.38/4.65  thf('375', plain,
% 4.38/4.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.65  thf('376', plain,
% 4.38/4.65      ((![X0 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup+', [status(thm)], ['374', '375'])).
% 4.38/4.65  thf('377', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65             (k1_zfmisc_1 @ 
% 4.38/4.65              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 4.38/4.65  thf('378', plain,
% 4.38/4.65      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65            (u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['376', '377'])).
% 4.38/4.65  thf('379', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('split', [status(esa)], ['91'])).
% 4.38/4.65  thf('380', plain,
% 4.38/4.65      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65            (u1_struct_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['378', '379'])).
% 4.38/4.65  thf('381', plain,
% 4.38/4.65      (((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65            (u1_struct_0 @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         | ~ (v2_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['352', '380'])).
% 4.38/4.65  thf('382', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['319', '320'])).
% 4.38/4.65  thf('383', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['372', '373'])).
% 4.38/4.65  thf('384', plain,
% 4.38/4.65      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['333', '334'])).
% 4.38/4.65  thf('385', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ sk_C_1 @ X0))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup+', [status(thm)], ['383', '384'])).
% 4.38/4.65  thf('386', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['372', '373'])).
% 4.38/4.65  thf('387', plain,
% 4.38/4.65      ((![X0 : $i]: (v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['385', '386'])).
% 4.38/4.65  thf('388', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('389', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('390', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('391', plain,
% 4.38/4.65      (((~ (v2_pre_topc @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)],
% 4.38/4.65                ['381', '382', '387', '388', '389', '390'])).
% 4.38/4.65  thf('392', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('393', plain,
% 4.38/4.65      (![X45 : $i]:
% 4.38/4.65         ((v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.65          | ~ (l1_pre_topc @ X45)
% 4.38/4.65          | ~ (v2_pre_topc @ X45))),
% 4.38/4.65      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.65  thf('394', plain,
% 4.38/4.65      ((((v2_pre_topc @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65         | ~ (l1_pre_topc @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup+', [status(thm)], ['392', '393'])).
% 4.38/4.65  thf('395', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('396', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('397', plain,
% 4.38/4.65      (((v2_pre_topc @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['394', '395', '396'])).
% 4.38/4.65  thf('398', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('399', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (l1_pre_topc @ X0)
% 4.38/4.65          | (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.65  thf('400', plain,
% 4.38/4.65      ((((l1_pre_topc @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (l1_pre_topc @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup+', [status(thm)], ['398', '399'])).
% 4.38/4.65  thf('401', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('402', plain,
% 4.38/4.65      (((l1_pre_topc @ (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['400', '401'])).
% 4.38/4.65  thf('403', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65         (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['391', '397', '402'])).
% 4.38/4.65  thf('404', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['350', '351'])).
% 4.38/4.65  thf('405', plain,
% 4.38/4.65      ((![X0 : $i]:
% 4.38/4.65          ((v5_pre_topc @ sk_C_1 @ sk_A @ X0)
% 4.38/4.65           | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65           | ~ (l1_pre_topc @ X0)
% 4.38/4.65           | ~ (v2_pre_topc @ X0)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)],
% 4.38/4.65                ['323', '324', '338', '339', '340', '341', '342', '343', 
% 4.38/4.65                 '344', '345'])).
% 4.38/4.65  thf('406', plain,
% 4.38/4.65      (((~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | ~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65         | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['404', '405'])).
% 4.38/4.65  thf('407', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('408', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('409', plain,
% 4.38/4.65      (((~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65            (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['406', '407', '408'])).
% 4.38/4.65  thf('410', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.65      inference('split', [status(esa)], ['93'])).
% 4.38/4.65  thf('411', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65           (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('clc', [status(thm)], ['409', '410'])).
% 4.38/4.65  thf('412', plain,
% 4.38/4.65      (~
% 4.38/4.65       ((v5_pre_topc @ sk_D @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 4.38/4.65       ~
% 4.38/4.65       ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 4.38/4.65       ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['403', '411'])).
% 4.38/4.65  thf('413', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 4.38/4.65       ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('split', [status(esa)], ['91'])).
% 4.38/4.65  thf('414', plain, (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.65      inference('sat_resolution*', [status(thm)], ['97', '101', '412', '413'])).
% 4.38/4.65  thf('415', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('simpl_trail', [status(thm)], ['88', '414'])).
% 4.38/4.65  thf('416', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.65  thf('417', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['22', '46'])).
% 4.38/4.65  thf('418', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65             (k1_zfmisc_1 @ 
% 4.38/4.65              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['9', '10', '13', '14', '15'])).
% 4.38/4.65  thf('419', plain,
% 4.38/4.65      ((~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65           (k1_zfmisc_1 @ 
% 4.38/4.65            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['417', '418'])).
% 4.38/4.65  thf('420', plain,
% 4.38/4.65      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65        (k1_zfmisc_1 @ 
% 4.38/4.65         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.65          (u1_struct_0 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['49', '52'])).
% 4.38/4.65  thf('421', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['419', '420'])).
% 4.38/4.65  thf('422', plain,
% 4.38/4.65      ((~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.65           (u1_struct_0 @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['416', '421'])).
% 4.38/4.65  thf('423', plain,
% 4.38/4.65      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 4.38/4.65        (u1_struct_0 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['71', '83', '84'])).
% 4.38/4.65  thf('424', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('demod', [status(thm)], ['422', '423'])).
% 4.38/4.65  thf('425', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('simplify', [status(thm)], ['424'])).
% 4.38/4.65  thf('426', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['415', '425'])).
% 4.38/4.65  thf('427', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('simplify', [status(thm)], ['426'])).
% 4.38/4.65  thf('428', plain,
% 4.38/4.65      ((~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['19', '427'])).
% 4.38/4.65  thf('429', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('430', plain,
% 4.38/4.65      ((((sk_C_1) = (k1_xboole_0))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['428', '429'])).
% 4.38/4.65  thf('431', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (~
% 4.38/4.65             ((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['94', '95'])).
% 4.38/4.65  thf('432', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (((v5_pre_topc @ sk_D @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['108', '109'])).
% 4.38/4.65  thf('433', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65         <= (~
% 4.38/4.65             ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('split', [status(esa)], ['100'])).
% 4.38/4.65  thf('434', plain,
% 4.38/4.65      (~
% 4.38/4.65       ((v5_pre_topc @ sk_D @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 4.38/4.65       ((v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['432', '433'])).
% 4.38/4.65  thf('435', plain,
% 4.38/4.65      (~
% 4.38/4.65       ((v5_pre_topc @ sk_D @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sat_resolution*', [status(thm)], ['97', '101', '412', '434'])).
% 4.38/4.65  thf('436', plain,
% 4.38/4.65      (~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 4.38/4.65      inference('simpl_trail', [status(thm)], ['431', '435'])).
% 4.38/4.65  thf('437', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('clc', [status(thm)], ['430', '436'])).
% 4.38/4.65  thf('438', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65        | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65        | ((sk_C_1) = (k1_xboole_0)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['18', '437'])).
% 4.38/4.65  thf('439', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('440', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('441', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('442', plain, (![X6 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('demod', [status(thm)], ['17', '441'])).
% 4.38/4.65  thf('443', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 4.38/4.65      inference('demod', [status(thm)], ['16', '442'])).
% 4.38/4.65  thf('444', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (l1_pre_topc @ X0)
% 4.38/4.65          | (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['1', '2'])).
% 4.38/4.65  thf('445', plain,
% 4.38/4.65      (![X45 : $i]:
% 4.38/4.65         ((v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45)))
% 4.38/4.65          | ~ (l1_pre_topc @ X45)
% 4.38/4.65          | ~ (v2_pre_topc @ X45))),
% 4.38/4.65      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 4.38/4.65  thf('446', plain,
% 4.38/4.65      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))
% 4.38/4.65         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)))),
% 4.38/4.65      inference('split', [status(esa)], ['20'])).
% 4.38/4.65  thf('447', plain, (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1))),
% 4.38/4.65      inference('sat_resolution*', [status(thm)], ['97', '101', '412', '413'])).
% 4.38/4.65  thf('448', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.38/4.65      inference('simpl_trail', [status(thm)], ['446', '447'])).
% 4.38/4.65  thf('449', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['31', '34', '37'])).
% 4.38/4.65  thf('450', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['31', '34', '37'])).
% 4.38/4.65  thf('451', plain,
% 4.38/4.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.65  thf('452', plain,
% 4.38/4.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X48)
% 4.38/4.65          | ~ (l1_pre_topc @ X48)
% 4.38/4.65          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 4.38/4.65          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 4.38/4.65          | (v5_pre_topc @ X47 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48)) @ X46)
% 4.38/4.65          | ~ (v5_pre_topc @ X47 @ X48 @ X46)
% 4.38/4.65          | ~ (m1_subset_1 @ X47 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ 
% 4.38/4.65                 (u1_struct_0 @ 
% 4.38/4.65                  (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.65                 (u1_struct_0 @ X46))))
% 4.38/4.65          | ~ (v1_funct_2 @ X47 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))) @ 
% 4.38/4.65               (u1_struct_0 @ X46))
% 4.38/4.65          | ~ (v1_funct_1 @ X47)
% 4.38/4.65          | ~ (l1_pre_topc @ X46)
% 4.38/4.65          | ~ (v2_pre_topc @ X46))),
% 4.38/4.65      inference('simplify', [status(thm)], ['7'])).
% 4.38/4.65  thf('453', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_1 @ k1_xboole_0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X0)
% 4.38/4.65          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['451', '452'])).
% 4.38/4.65  thf('454', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['171', '172'])).
% 4.38/4.65  thf('455', plain,
% 4.38/4.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.38/4.65  thf('456', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('demod', [status(thm)], ['453', '454', '455'])).
% 4.38/4.65  thf('457', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (v1_funct_2 @ k1_xboole_0 @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65             k1_xboole_0)
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65          | ~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 4.38/4.65               (u1_struct_0 @ sk_B_1))
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1)
% 4.38/4.65          | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65          | ~ (v2_pre_topc @ sk_B_1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['450', '456'])).
% 4.38/4.65  thf('458', plain,
% 4.38/4.65      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['216', '217'])).
% 4.38/4.65  thf('459', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('460', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('461', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65          | ~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 4.38/4.65               (u1_struct_0 @ sk_B_1))
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['457', '458', '459', '460'])).
% 4.38/4.65  thf('462', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X0) @ k1_xboole_0)
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1)
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v2_pre_topc @ X0)
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['449', '461'])).
% 4.38/4.65  thf('463', plain,
% 4.38/4.65      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['216', '217'])).
% 4.38/4.65  thf('464', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1)
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v2_pre_topc @ X0)
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['462', '463'])).
% 4.38/4.65  thf('465', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | (v5_pre_topc @ k1_xboole_0 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1)
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('simplify', [status(thm)], ['464'])).
% 4.38/4.65  thf('466', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('467', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('468', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (v5_pre_topc @ sk_C_1 @ X0 @ sk_B_1)
% 4.38/4.65          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['465', '466', '467'])).
% 4.38/4.65  thf('469', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['237', '240', '243'])).
% 4.38/4.65  thf('470', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('471', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('472', plain, (((k1_relat_1 @ sk_C_1) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['469', '470', '471'])).
% 4.38/4.65  thf('473', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 4.38/4.65          | ~ (v5_pre_topc @ sk_C_1 @ X0 @ sk_B_1)
% 4.38/4.65          | ((sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['468', '472'])).
% 4.38/4.65  thf('474', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 4.38/4.65        | ~ (l1_pre_topc @ sk_A)
% 4.38/4.65        | ~ (v2_pre_topc @ sk_A))),
% 4.38/4.65      inference('sup-', [status(thm)], ['448', '473'])).
% 4.38/4.65  thf('475', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('476', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('477', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['474', '475', '476'])).
% 4.38/4.65  thf('478', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['31', '34', '37'])).
% 4.38/4.65  thf('479', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('480', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1))
% 4.38/4.65        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['478', '479'])).
% 4.38/4.65  thf('481', plain, (((k1_relat_1 @ sk_C_1) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['469', '470', '471'])).
% 4.38/4.65  thf('482', plain,
% 4.38/4.65      ((((u1_struct_0 @ sk_B_1) = (sk_C_1)) | ((sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('demod', [status(thm)], ['480', '481'])).
% 4.38/4.65  thf('483', plain,
% 4.38/4.65      ((m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65        (k1_zfmisc_1 @ 
% 4.38/4.65         (k2_zfmisc_1 @ 
% 4.38/4.65          (u1_struct_0 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65          (u1_struct_0 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 4.38/4.65      inference('demod', [status(thm)], ['4', '5'])).
% 4.38/4.65  thf('484', plain,
% 4.38/4.65      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X52)
% 4.38/4.65          | ~ (l1_pre_topc @ X52)
% 4.38/4.65          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.65          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.65          | (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.65          | ~ (v5_pre_topc @ X51 @ X52 @ X50)
% 4.38/4.65          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.65                 (u1_struct_0 @ 
% 4.38/4.65                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.65          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.65          | ~ (v1_funct_1 @ X51)
% 4.38/4.65          | ~ (l1_pre_topc @ X50)
% 4.38/4.65          | ~ (v2_pre_topc @ X50))),
% 4.38/4.65      inference('simplify', [status(thm)], ['55'])).
% 4.38/4.65  thf('485', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65        | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65        | ~ (v1_funct_1 @ sk_C_1)
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65             sk_B_1)
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65             (k1_zfmisc_1 @ 
% 4.38/4.65              (k2_zfmisc_1 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65               (u1_struct_0 @ sk_B_1))))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65             (u1_struct_0 @ sk_B_1))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['483', '484'])).
% 4.38/4.65  thf('486', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('487', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('488', plain, ((v1_funct_1 @ sk_C_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('489', plain,
% 4.38/4.65      ((v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65        (u1_struct_0 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65        (u1_struct_0 @ 
% 4.38/4.65         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['11', '12'])).
% 4.38/4.65  thf('490', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.38/4.65             (k1_zfmisc_1 @ 
% 4.38/4.65              (k2_zfmisc_1 @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65               (u1_struct_0 @ sk_B_1))))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65             (u1_struct_0 @ sk_B_1))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.65      inference('demod', [status(thm)], ['485', '486', '487', '488', '489'])).
% 4.38/4.65  thf('491', plain, (![X6 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('demod', [status(thm)], ['17', '441'])).
% 4.38/4.65  thf('492', plain,
% 4.38/4.65      ((~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65             (u1_struct_0 @ 
% 4.38/4.65              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65             (u1_struct_0 @ sk_B_1))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.65      inference('demod', [status(thm)], ['490', '491'])).
% 4.38/4.65  thf('493', plain,
% 4.38/4.65      ((~ (v1_funct_2 @ sk_C_1 @ 
% 4.38/4.65           (u1_struct_0 @ 
% 4.38/4.65            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 4.38/4.65           sk_C_1)
% 4.38/4.65        | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65             sk_B_1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['482', '492'])).
% 4.38/4.65  thf('494', plain,
% 4.38/4.65      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['216', '217'])).
% 4.38/4.65  thf('495', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('496', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('497', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_1 @ X0 @ sk_C_1)),
% 4.38/4.65      inference('demod', [status(thm)], ['494', '495', '496'])).
% 4.38/4.65  thf('498', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65             sk_B_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['493', '497'])).
% 4.38/4.65  thf('499', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ((sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['477', '498'])).
% 4.38/4.65  thf('500', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ((sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('simplify', [status(thm)], ['499'])).
% 4.38/4.65  thf('501', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ sk_A)
% 4.38/4.65        | ~ (l1_pre_topc @ sk_A)
% 4.38/4.65        | ((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['445', '500'])).
% 4.38/4.65  thf('502', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('503', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('504', plain,
% 4.38/4.65      ((((sk_C_1) = (u1_struct_0 @ sk_A))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.38/4.65      inference('demod', [status(thm)], ['501', '502', '503'])).
% 4.38/4.65  thf('505', plain,
% 4.38/4.65      (~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 4.38/4.65      inference('simpl_trail', [status(thm)], ['431', '435'])).
% 4.38/4.65  thf('506', plain,
% 4.38/4.65      ((~ (l1_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.38/4.65        | ((sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('clc', [status(thm)], ['504', '505'])).
% 4.38/4.65  thf('507', plain,
% 4.38/4.65      ((~ (l1_pre_topc @ sk_A) | ((sk_C_1) = (u1_struct_0 @ sk_A)))),
% 4.38/4.65      inference('sup-', [status(thm)], ['444', '506'])).
% 4.38/4.65  thf('508', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('509', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('510', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('511', plain,
% 4.38/4.65      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.38/4.65      inference('sup+', [status(thm)], ['333', '334'])).
% 4.38/4.65  thf('512', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('513', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('514', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0)),
% 4.38/4.65      inference('demod', [status(thm)], ['511', '512', '513'])).
% 4.38/4.65  thf('515', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['443', '509', '510', '514'])).
% 4.38/4.65  thf('516', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.38/4.65      inference('simpl_trail', [status(thm)], ['446', '447'])).
% 4.38/4.65  thf('517', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('518', plain,
% 4.38/4.65      (![X36 : $i, X37 : $i]:
% 4.38/4.65         (m1_subset_1 @ (sk_C @ X36 @ X37) @ 
% 4.38/4.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))),
% 4.38/4.65      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.65  thf('519', plain,
% 4.38/4.65      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X52)
% 4.38/4.65          | ~ (l1_pre_topc @ X52)
% 4.38/4.65          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))
% 4.38/4.65          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X50))))
% 4.38/4.65          | (v5_pre_topc @ X51 @ X52 @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50)))
% 4.38/4.65          | ~ (v5_pre_topc @ X51 @ X52 @ X50)
% 4.38/4.65          | ~ (m1_subset_1 @ X51 @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ 
% 4.38/4.65                 (u1_struct_0 @ 
% 4.38/4.65                  (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))))
% 4.38/4.65          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X52) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X50) @ (u1_pre_topc @ X50))))
% 4.38/4.65          | ~ (v1_funct_1 @ X51)
% 4.38/4.65          | ~ (l1_pre_topc @ X50)
% 4.38/4.65          | ~ (v2_pre_topc @ X50))),
% 4.38/4.65      inference('simplify', [status(thm)], ['55'])).
% 4.38/4.65  thf('520', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v1_funct_1 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)))
% 4.38/4.65          | ~ (v1_funct_2 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               (u1_struct_0 @ X1) @ 
% 4.38/4.65               (u1_struct_0 @ 
% 4.38/4.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 4.38/4.65          | ~ (v5_pre_topc @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               X1 @ X0)
% 4.38/4.65          | (v5_pre_topc @ 
% 4.38/4.65             (sk_C @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65              (u1_struct_0 @ X1)) @ 
% 4.38/4.65             X1 @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | ~ (m1_subset_1 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 4.38/4.65          | ~ (v1_funct_2 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['518', '519'])).
% 4.38/4.65  thf('521', plain, (![X36 : $i, X37 : $i]: (v1_funct_1 @ (sk_C @ X36 @ X37))),
% 4.38/4.65      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.65  thf('522', plain,
% 4.38/4.65      (![X36 : $i, X37 : $i]: (v1_funct_2 @ (sk_C @ X36 @ X37) @ X37 @ X36)),
% 4.38/4.65      inference('cnf', [status(esa)], [rc1_funct_2])).
% 4.38/4.65  thf('523', plain,
% 4.38/4.65      (![X0 : $i, X1 : $i]:
% 4.38/4.65         (~ (v2_pre_topc @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v5_pre_topc @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               X1 @ X0)
% 4.38/4.65          | (v5_pre_topc @ 
% 4.38/4.65             (sk_C @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65              (u1_struct_0 @ X1)) @ 
% 4.38/4.65             X1 @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | ~ (m1_subset_1 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               (k1_zfmisc_1 @ 
% 4.38/4.65                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 4.38/4.65          | ~ (v1_funct_2 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ X1)) @ 
% 4.38/4.65               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 4.38/4.65          | ~ (l1_pre_topc @ X1)
% 4.38/4.65          | ~ (v2_pre_topc @ X1))),
% 4.38/4.65      inference('demod', [status(thm)], ['520', '521', '522'])).
% 4.38/4.65  thf('524', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         (~ (m1_subset_1 @ 
% 4.38/4.65             (sk_C @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65              (u1_struct_0 @ sk_A)) @ 
% 4.38/4.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ (u1_struct_0 @ X0))))
% 4.38/4.65          | ~ (v2_pre_topc @ sk_A)
% 4.38/4.65          | ~ (l1_pre_topc @ sk_A)
% 4.38/4.65          | ~ (v1_funct_2 @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ sk_A)) @ 
% 4.38/4.65               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 4.38/4.65          | (v5_pre_topc @ 
% 4.38/4.65             (sk_C @ 
% 4.38/4.65              (u1_struct_0 @ 
% 4.38/4.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65              (u1_struct_0 @ sk_A)) @ 
% 4.38/4.65             sk_A @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | ~ (v5_pre_topc @ 
% 4.38/4.65               (sk_C @ 
% 4.38/4.65                (u1_struct_0 @ 
% 4.38/4.65                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 4.38/4.65                (u1_struct_0 @ sk_A)) @ 
% 4.38/4.65               sk_A @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v2_pre_topc @ X0))),
% 4.38/4.65      inference('sup-', [status(thm)], ['517', '523'])).
% 4.38/4.65  thf('525', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('526', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.38/4.65      inference('sup-', [status(thm)], ['326', '332'])).
% 4.38/4.65  thf('527', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('528', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('529', plain, (![X0 : $i]: ((sk_C @ X0 @ sk_C_1) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['526', '527', '528'])).
% 4.38/4.65  thf('530', plain,
% 4.38/4.65      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 4.38/4.65      inference('simplify', [status(thm)], ['327'])).
% 4.38/4.65  thf('531', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('532', plain, (((sk_C_1) = (k1_xboole_0))),
% 4.38/4.65      inference('demod', [status(thm)], ['438', '439', '440'])).
% 4.38/4.65  thf('533', plain, (![X5 : $i]: ((k2_zfmisc_1 @ sk_C_1 @ X5) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['530', '531', '532'])).
% 4.38/4.65  thf('534', plain, (![X6 : $i]: (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X6))),
% 4.38/4.65      inference('demod', [status(thm)], ['17', '441'])).
% 4.38/4.65  thf('535', plain, ((v2_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('536', plain, ((l1_pre_topc @ sk_A)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('537', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('538', plain, (![X0 : $i]: ((sk_C @ X0 @ sk_C_1) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['526', '527', '528'])).
% 4.38/4.65  thf('539', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('540', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_1 @ sk_C_1 @ X0)),
% 4.38/4.65      inference('demod', [status(thm)], ['511', '512', '513'])).
% 4.38/4.65  thf('541', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('542', plain, (![X0 : $i]: ((sk_C @ X0 @ sk_C_1) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['526', '527', '528'])).
% 4.38/4.65  thf('543', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('544', plain, (![X0 : $i]: ((sk_C @ X0 @ sk_C_1) = (sk_C_1))),
% 4.38/4.65      inference('demod', [status(thm)], ['526', '527', '528'])).
% 4.38/4.65  thf('545', plain,
% 4.38/4.65      (![X0 : $i]:
% 4.38/4.65         ((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.38/4.65          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ X0)
% 4.38/4.65          | ~ (l1_pre_topc @ X0)
% 4.38/4.65          | ~ (v2_pre_topc @ X0))),
% 4.38/4.65      inference('demod', [status(thm)],
% 4.38/4.65                ['524', '525', '529', '533', '534', '535', '536', '537', 
% 4.38/4.65                 '538', '539', '540', '541', '542', '543', '544'])).
% 4.38/4.65  thf('546', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ sk_B_1)
% 4.38/4.65        | ~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['516', '545'])).
% 4.38/4.65  thf('547', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('548', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('549', plain,
% 4.38/4.65      ((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 4.38/4.65        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 4.38/4.65      inference('demod', [status(thm)], ['546', '547', '548'])).
% 4.38/4.65  thf('550', plain,
% 4.38/4.65      ((~ (v2_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (l1_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65           (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('demod', [status(thm)], ['515', '549'])).
% 4.38/4.65  thf('551', plain,
% 4.38/4.65      (~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 4.38/4.65      inference('simpl_trail', [status(thm)], ['431', '435'])).
% 4.38/4.65  thf('552', plain, (((sk_C_1) = (u1_struct_0 @ sk_A))),
% 4.38/4.65      inference('demod', [status(thm)], ['507', '508'])).
% 4.38/4.65  thf('553', plain,
% 4.38/4.65      (~ (v5_pre_topc @ sk_C_1 @ 
% 4.38/4.65          (g1_pre_topc @ sk_C_1 @ (u1_pre_topc @ sk_A)) @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 4.38/4.65      inference('demod', [status(thm)], ['551', '552'])).
% 4.38/4.65  thf('554', plain,
% 4.38/4.65      ((~ (l1_pre_topc @ 
% 4.38/4.65           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('clc', [status(thm)], ['550', '553'])).
% 4.38/4.65  thf('555', plain,
% 4.38/4.65      ((~ (l1_pre_topc @ sk_B_1)
% 4.38/4.65        | ~ (v2_pre_topc @ 
% 4.38/4.65             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 4.38/4.65      inference('sup-', [status(thm)], ['3', '554'])).
% 4.38/4.65  thf('556', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('557', plain,
% 4.38/4.65      (~ (v2_pre_topc @ 
% 4.38/4.65          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 4.38/4.65      inference('demod', [status(thm)], ['555', '556'])).
% 4.38/4.65  thf('558', plain, ((~ (v2_pre_topc @ sk_B_1) | ~ (l1_pre_topc @ sk_B_1))),
% 4.38/4.65      inference('sup-', [status(thm)], ['0', '557'])).
% 4.38/4.65  thf('559', plain, ((v2_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('560', plain, ((l1_pre_topc @ sk_B_1)),
% 4.38/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.38/4.65  thf('561', plain, ($false),
% 4.38/4.65      inference('demod', [status(thm)], ['558', '559', '560'])).
% 4.38/4.65  
% 4.38/4.65  % SZS output end Refutation
% 4.38/4.65  
% 4.48/4.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
