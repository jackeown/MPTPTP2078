%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NfeHFfIaSQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:29 EST 2020

% Result     : Theorem 36.30s
% Output     : Refutation 36.32s
% Verified   : 
% Statistics : Number of formulae       :  557 (29905377 expanded)
%              Number of leaves         :   46 (8496745 expanded)
%              Depth                    :   74
%              Number of atoms          : 9083 (1007864774 expanded)
%              Number of equality atoms :  175 (14222341 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X37 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X38: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_C_2 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v5_pre_topc @ X42 @ X41 @ X39 )
      | ( v5_pre_topc @ X40 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X39 )
      | ( X42 != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('13',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( v5_pre_topc @ X40 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X39 )
      | ~ ( v5_pre_topc @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_C_2 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X38: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('26',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_partfun1 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_partfun1 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_partfun1 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('35',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v4_relat_1 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v4_relat_1 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['36','41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v4_relat_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['39','40'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

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

thf('75',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X46 @ X45 @ X43 )
      | ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ( X46 != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('76',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( v5_pre_topc @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( v1_xboole_0 @ sk_C_2 )
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
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ X1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85','86'])).

thf('88',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','89'])).

thf('91',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','91'])).

thf('93',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_C_2 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    sk_C_2 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_C_2 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,(
    ! [X38: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('109',plain,(
    ! [X38: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('110',plain,
    ( ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('111',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('112',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('113',plain,(
    sk_C_2 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('116',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('117',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v5_pre_topc @ X40 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X39 )
      | ( v5_pre_topc @ X42 @ X41 @ X39 )
      | ( X42 != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('118',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( v5_pre_topc @ X40 @ X41 @ X39 )
      | ~ ( v5_pre_topc @ X40 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['116','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('125',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['115','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['114','128'])).

thf('130',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['111','129'])).

thf('131',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['110','131'])).

thf('133',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['109','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['108','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('142',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('143',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('144',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('145',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ( v5_pre_topc @ X46 @ X45 @ X43 )
      | ( X46 != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('146',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v5_pre_topc @ X44 @ X45 @ X43 )
      | ~ ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( v1_xboole_0 @ sk_C_2 )
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
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156'])).

thf('158',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('159',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['141','159'])).

thf('161',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['140','161'])).

thf('163',plain,
    ( ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['97'])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('166',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('167',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('168',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('170',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('172',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['167','172'])).

thf('174',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('175',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('177',plain,
    ( ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('184',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('185',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('187',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('189',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_2 ) )
        | ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['183','189'])).

thf('191',plain,
    ( ( ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['182','190'])).

thf('192',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('193',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('194',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['193'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('195',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('196',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('198',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('202',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_2 @ ( sk_C_1 @ X0 @ X1 ) @ X1 @ X0 )
      | ( v1_partfun1 @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('205',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_funct_2 @ ( sk_C_1 @ X33 @ X34 ) @ X34 @ X33 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_partfun1 @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v4_relat_1 @ ( sk_C_1 @ X1 @ X0 ) @ X0 )
      | ( ( k1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('210',plain,(
    ! [X33: $i,X34: $i] :
      ( v4_relat_1 @ ( sk_C_1 @ X33 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( ( k1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['200','211'])).

thf('213',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['214'])).

thf('216',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['192','215'])).

thf('217',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('218',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['191','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('221',plain,(
    ! [X38: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('222',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('223',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('224',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_funct_2 @ ( sk_C_1 @ X33 @ X34 ) @ X34 @ X33 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('230',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_funct_2 @ sk_C_2 @ X1 @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['222','229'])).

thf('231',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('233',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('234',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v5_pre_topc @ X44 @ X45 @ X43 )
      | ~ ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('235',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['235','236','237','238'])).

thf('240',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('241',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['232','241'])).

thf('243',plain,
    ( ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ sk_C_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['231','242'])).

thf('244',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['230','243'])).

thf('245',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('246',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['221','246'])).

thf('248',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['220','250'])).

thf('252',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['219','253'])).

thf('255',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['191','218'])).

thf('256',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('257',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('259',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = sk_C_2 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('261',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( v5_pre_topc @ X40 @ X41 @ X39 )
      | ~ ( v5_pre_topc @ X40 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X0 )
      | ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['184'])).

thf('264',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('265',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('267',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('271',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X0 )
      | ( v5_pre_topc @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['262','271','272'])).

thf('274',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ sk_C_2 )
        | ( sk_C_2
          = ( u1_struct_0 @ sk_A ) )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1 )
        | ~ ( v5_pre_topc @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
        | ~ ( l1_pre_topc @ sk_B_1 )
        | ~ ( v2_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['259','273'])).

thf('275',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('276',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('278',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_funct_2 @ ( sk_C_1 @ X33 @ X34 ) @ X34 @ X33 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('279',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('280',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['276','279'])).

thf('281',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('282',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_2 @ X0 @ sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['280','281'])).

thf('283',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('284',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('285',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('286',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2
          = ( u1_struct_0 @ sk_A ) )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
        | ( v5_pre_topc @ sk_C_2 @ X0 @ sk_B_1 )
        | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['274','275','282','283','284','285','286','287'])).

thf('289',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( sk_C_2
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['254','288'])).

thf('290',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( ( sk_C_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ( sk_C_2
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['289','290','291','292'])).

thf('294',plain,
    ( ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ( sk_C_2
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['97'])).

thf('296',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('299',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_funct_2 @ ( sk_C_1 @ X33 @ X34 ) @ X34 @ X33 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('300',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['298','299'])).

thf('301',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ sk_C_2 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['297','300'])).

thf('302',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('303',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,
    ( ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['177','296','303'])).

thf('305',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','304'])).

thf('306',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','307'])).

thf('309',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('313',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('314',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('315',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('318',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v5_pre_topc @ X44 @ X45 @ X43 )
      | ~ ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('320',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ sk_A @ X0 )
        | ~ ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['312','320'])).

thf('322',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('323',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('324',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['193'])).

thf('325',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['323','324'])).

thf('326',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('327',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('328',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('329',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('332',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('333',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('334',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('335',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('336',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('337',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('338',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('339',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['167','172'])).

thf('340',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('341',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('342',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('343',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('344',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('345',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_C_2 @ X0 )
        = sk_C_2 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('346',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ sk_C_2 @ sk_A @ X0 )
        | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['321','322','327','328','329','330','331','332','333','334','335','336','337','338','339','340','341','342','343','344','345','346'])).

thf('348',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['311','347'])).

thf('349',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['348','349','350'])).

thf('352',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['97'])).

thf('353',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['95'])).

thf('355',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['101','105','353','354'])).

thf('356',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['92','355'])).

thf('357',plain,
    ( ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('358',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('359',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('360',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('361',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['359','360'])).

thf('362',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('363',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['361','362'])).

thf('364',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['358','363'])).

thf('365',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['364'])).

thf('366',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['357','365'])).

thf('367',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['366'])).

thf('368',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['356','367'])).

thf('369',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['368'])).

thf('370',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','369'])).

thf('371',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['370','371'])).

thf('373',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('374',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('375',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['104'])).

thf('376',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['101','105','353','376'])).

thf('378',plain,(
    ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['373','377'])).

thf('379',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['372','378'])).

thf('380',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','379'])).

thf('381',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['380','381','382'])).

thf('384',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['23','383'])).

thf('385',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('386',plain,(
    ! [X38: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('387',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('389',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('390',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('392',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( v5_pre_topc @ X40 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X39 )
      | ~ ( v5_pre_topc @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('393',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ k1_xboole_0 ) ) )
      | ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_B_1 )
      | ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['391','392'])).

thf('394',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['184'])).

thf('395',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_B_1 )
      | ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['393','394','395','396'])).

thf('398',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['390','397'])).

thf('399',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_B_1 )
      | ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k1_relat_1 @ sk_C_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['398'])).

thf('400',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['387','399'])).

thf('401',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,
    ( ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('405',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['101','105','353','354'])).

thf('406',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['404','405'])).

thf('407',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('408',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['400','401','402','403','406','407'])).

thf('409',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['380','381','382'])).

thf('410',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('411',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('412',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('413',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('414',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['408','411','412','413'])).

thf('415',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('416',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('417',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('418',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_2 @ X0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['415','416','417'])).

thf('419',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['214'])).

thf('420',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('421',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('422',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['419','420','421'])).

thf('423',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['414','418','422'])).

thf('424',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('425',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('426',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ sk_C_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['424','425'])).

thf('427',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('428',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('429',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( v5_pre_topc @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('430',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['428','429'])).

thf('431',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('432',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('433',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['430','431','432','433'])).

thf('435',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('436',plain,
    ( ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['434','435'])).

thf('437',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['427','436'])).

thf('438',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['380','381','382'])).

thf('439',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['437','438'])).

thf('440',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['426','439'])).

thf('441',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['423','440'])).

thf('442',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( sk_C_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['386','441'])).

thf('443',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('445',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( sk_C_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['442','443','444'])).

thf('446',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['385','445'])).

thf('447',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('448',plain,
    ( ( sk_C_2
      = ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['446','447'])).

thf('449',plain,(
    ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['373','377'])).

thf('450',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_C_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['448','449'])).

thf('451',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('452',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['419','420','421'])).

thf('453',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_C_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['451','452'])).

thf('454',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('455',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['298','299'])).

thf('456',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('457',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('458',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 ) ),
    inference(demod,[status(thm)],['455','456','457'])).

thf('459',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('460',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ sk_C_2 @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['384','454','458','459'])).

thf('461',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['404','405'])).

thf('462',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('463',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('464',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v5_pre_topc @ X44 @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( v5_pre_topc @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('465',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ X1 @ X0 )
      | ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['463','464'])).

thf('466',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ sk_C_2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['462','465'])).

thf('467',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('468',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['193'])).

thf('469',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('470',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('471',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('472',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 ) ),
    inference(demod,[status(thm)],['455','456','457'])).

thf('473',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('474',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('475',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('476',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('477',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('478',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0 ) ),
    inference(demod,[status(thm)],['455','456','457'])).

thf('479',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('480',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('481',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('482',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('483',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('484',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['409','410'])).

thf('485',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['483','484'])).

thf('486',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('487',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('488',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('489',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('490',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('491',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ sk_C_2 @ X10 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['468','469','470'])).

thf('492',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('493',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['466','467','471','472','473','474','475','476','477','478','479','480','481','482','485','486','487','488','489','490','491','492'])).

thf('494',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['461','493'])).

thf('495',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('496',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('497',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['494','495','496'])).

thf('498',plain,
    ( ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ sk_C_2 @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['460','497'])).

thf('499',plain,(
    ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['373','377'])).

thf('500',plain,
    ( sk_C_2
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['450','453'])).

thf('501',plain,(
    ~ ( v5_pre_topc @ sk_C_2 @ ( g1_pre_topc @ sk_C_2 @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['499','500'])).

thf('502',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['498','501'])).

thf('503',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','502'])).

thf('504',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('505',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('506',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['503','504','505'])).

thf('507',plain,(
    ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','506'])).

thf('508',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,(
    $false ),
    inference(demod,[status(thm)],['507','508'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NfeHFfIaSQ
% 0.16/0.39  % Computer   : n007.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 18:40:51 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 36.30/36.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.30/36.51  % Solved by: fo/fo7.sh
% 36.30/36.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.30/36.51  % done 21351 iterations in 36.029s
% 36.30/36.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.30/36.51  % SZS output start Refutation
% 36.30/36.51  thf(sk_A_type, type, sk_A: $i).
% 36.30/36.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 36.30/36.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.30/36.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 36.30/36.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.30/36.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.30/36.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 36.30/36.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 36.30/36.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 36.30/36.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 36.30/36.51  thf(sk_D_type, type, sk_D: $i).
% 36.30/36.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 36.30/36.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 36.30/36.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 36.30/36.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 36.30/36.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 36.30/36.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 36.30/36.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 36.30/36.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 36.30/36.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 36.30/36.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.30/36.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 36.30/36.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 36.30/36.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 36.30/36.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 36.30/36.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 36.30/36.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 36.30/36.51  thf(dt_u1_pre_topc, axiom,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( l1_pre_topc @ A ) =>
% 36.30/36.51       ( m1_subset_1 @
% 36.30/36.51         ( u1_pre_topc @ A ) @ 
% 36.30/36.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 36.30/36.51  thf('0', plain,
% 36.30/36.51      (![X37 : $i]:
% 36.30/36.51         ((m1_subset_1 @ (u1_pre_topc @ X37) @ 
% 36.30/36.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37))))
% 36.30/36.51          | ~ (l1_pre_topc @ X37))),
% 36.30/36.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 36.30/36.51  thf(dt_g1_pre_topc, axiom,
% 36.30/36.51    (![A:$i,B:$i]:
% 36.30/36.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 36.30/36.51       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 36.30/36.51         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 36.30/36.51  thf('1', plain,
% 36.30/36.51      (![X35 : $i, X36 : $i]:
% 36.30/36.51         ((l1_pre_topc @ (g1_pre_topc @ X35 @ X36))
% 36.30/36.51          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X35))))),
% 36.30/36.51      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 36.30/36.51  thf('2', plain,
% 36.30/36.51      (![X0 : $i]:
% 36.30/36.51         (~ (l1_pre_topc @ X0)
% 36.30/36.51          | (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['0', '1'])).
% 36.30/36.51  thf(fc6_pre_topc, axiom,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.30/36.51       ( ( v1_pre_topc @
% 36.30/36.51           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 36.30/36.51         ( v2_pre_topc @
% 36.30/36.51           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 36.30/36.51  thf('3', plain,
% 36.30/36.51      (![X38 : $i]:
% 36.30/36.51         ((v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 36.30/36.51          | ~ (l1_pre_topc @ X38)
% 36.30/36.51          | ~ (v2_pre_topc @ X38))),
% 36.30/36.51      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 36.30/36.51  thf(d3_tarski, axiom,
% 36.30/36.51    (![A:$i,B:$i]:
% 36.30/36.51     ( ( r1_tarski @ A @ B ) <=>
% 36.30/36.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 36.30/36.51  thf('4', plain,
% 36.30/36.51      (![X4 : $i, X6 : $i]:
% 36.30/36.51         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 36.30/36.51      inference('cnf', [status(esa)], [d3_tarski])).
% 36.30/36.51  thf(d1_xboole_0, axiom,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 36.30/36.51  thf('5', plain,
% 36.30/36.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 36.30/36.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 36.30/36.51  thf('6', plain,
% 36.30/36.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 36.30/36.51      inference('sup-', [status(thm)], ['4', '5'])).
% 36.30/36.51  thf(t3_subset, axiom,
% 36.30/36.51    (![A:$i,B:$i]:
% 36.30/36.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.30/36.51  thf('7', plain,
% 36.30/36.51      (![X11 : $i, X13 : $i]:
% 36.30/36.51         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 36.30/36.51      inference('cnf', [status(esa)], [t3_subset])).
% 36.30/36.51  thf('8', plain,
% 36.30/36.51      (![X0 : $i, X1 : $i]:
% 36.30/36.51         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 36.30/36.51      inference('sup-', [status(thm)], ['6', '7'])).
% 36.30/36.51  thf(t64_pre_topc, conjecture,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.30/36.51       ( ![B:$i]:
% 36.30/36.51         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 36.30/36.51           ( ![C:$i]:
% 36.30/36.51             ( ( ( v1_funct_1 @ C ) & 
% 36.30/36.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 36.30/36.51                 ( m1_subset_1 @
% 36.30/36.51                   C @ 
% 36.30/36.51                   ( k1_zfmisc_1 @
% 36.30/36.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 36.30/36.51               ( ![D:$i]:
% 36.30/36.51                 ( ( ( v1_funct_1 @ D ) & 
% 36.30/36.51                     ( v1_funct_2 @
% 36.30/36.51                       D @ 
% 36.30/36.51                       ( u1_struct_0 @
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 36.30/36.51                       ( u1_struct_0 @
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 36.30/36.51                     ( m1_subset_1 @
% 36.30/36.51                       D @ 
% 36.30/36.51                       ( k1_zfmisc_1 @
% 36.30/36.51                         ( k2_zfmisc_1 @
% 36.30/36.51                           ( u1_struct_0 @
% 36.30/36.51                             ( g1_pre_topc @
% 36.30/36.51                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 36.30/36.51                           ( u1_struct_0 @
% 36.30/36.51                             ( g1_pre_topc @
% 36.30/36.51                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 36.30/36.51                   ( ( ( C ) = ( D ) ) =>
% 36.30/36.51                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 36.30/36.51                       ( v5_pre_topc @
% 36.30/36.51                         D @ 
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 36.30/36.51  thf(zf_stmt_0, negated_conjecture,
% 36.30/36.51    (~( ![A:$i]:
% 36.30/36.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.30/36.51          ( ![B:$i]:
% 36.30/36.51            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 36.30/36.51              ( ![C:$i]:
% 36.30/36.51                ( ( ( v1_funct_1 @ C ) & 
% 36.30/36.51                    ( v1_funct_2 @
% 36.30/36.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 36.30/36.51                    ( m1_subset_1 @
% 36.30/36.51                      C @ 
% 36.30/36.51                      ( k1_zfmisc_1 @
% 36.30/36.51                        ( k2_zfmisc_1 @
% 36.30/36.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 36.30/36.51                  ( ![D:$i]:
% 36.30/36.51                    ( ( ( v1_funct_1 @ D ) & 
% 36.30/36.51                        ( v1_funct_2 @
% 36.30/36.51                          D @ 
% 36.30/36.51                          ( u1_struct_0 @
% 36.30/36.51                            ( g1_pre_topc @
% 36.30/36.51                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 36.30/36.51                          ( u1_struct_0 @
% 36.30/36.51                            ( g1_pre_topc @
% 36.30/36.51                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 36.30/36.51                        ( m1_subset_1 @
% 36.30/36.51                          D @ 
% 36.30/36.51                          ( k1_zfmisc_1 @
% 36.30/36.51                            ( k2_zfmisc_1 @
% 36.30/36.51                              ( u1_struct_0 @
% 36.30/36.51                                ( g1_pre_topc @
% 36.30/36.51                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 36.30/36.51                              ( u1_struct_0 @
% 36.30/36.51                                ( g1_pre_topc @
% 36.30/36.51                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 36.30/36.51                      ( ( ( C ) = ( D ) ) =>
% 36.30/36.51                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 36.30/36.51                          ( v5_pre_topc @
% 36.30/36.51                            D @ 
% 36.30/36.51                            ( g1_pre_topc @
% 36.30/36.51                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 36.30/36.51                            ( g1_pre_topc @
% 36.30/36.51                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 36.30/36.51    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 36.30/36.51  thf('9', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_D @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('10', plain, (((sk_C_2) = (sk_D))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('11', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('demod', [status(thm)], ['9', '10'])).
% 36.30/36.51  thf(t62_pre_topc, axiom,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.30/36.51       ( ![B:$i]:
% 36.30/36.51         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 36.30/36.51           ( ![C:$i]:
% 36.30/36.51             ( ( ( v1_funct_1 @ C ) & 
% 36.30/36.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 36.30/36.51                 ( m1_subset_1 @
% 36.30/36.51                   C @ 
% 36.30/36.51                   ( k1_zfmisc_1 @
% 36.30/36.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 36.30/36.51               ( ![D:$i]:
% 36.30/36.51                 ( ( ( v1_funct_1 @ D ) & 
% 36.30/36.51                     ( v1_funct_2 @
% 36.30/36.51                       D @ 
% 36.30/36.51                       ( u1_struct_0 @
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 36.30/36.51                       ( u1_struct_0 @ B ) ) & 
% 36.30/36.51                     ( m1_subset_1 @
% 36.30/36.51                       D @ 
% 36.30/36.51                       ( k1_zfmisc_1 @
% 36.30/36.51                         ( k2_zfmisc_1 @
% 36.30/36.51                           ( u1_struct_0 @
% 36.30/36.51                             ( g1_pre_topc @
% 36.30/36.51                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 36.30/36.51                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 36.30/36.51                   ( ( ( C ) = ( D ) ) =>
% 36.30/36.51                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 36.30/36.51                       ( v5_pre_topc @
% 36.30/36.51                         D @ 
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 36.30/36.51                         B ) ) ) ) ) ) ) ) ) ))).
% 36.30/36.51  thf('12', plain,
% 36.30/36.51      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 36.30/36.51         (~ (v2_pre_topc @ X39)
% 36.30/36.51          | ~ (l1_pre_topc @ X39)
% 36.30/36.51          | ~ (v1_funct_1 @ X40)
% 36.30/36.51          | ~ (v1_funct_2 @ X40 @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.30/36.51               (u1_struct_0 @ X39))
% 36.30/36.51          | ~ (m1_subset_1 @ X40 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ 
% 36.30/36.51                 (u1_struct_0 @ 
% 36.30/36.51                  (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.30/36.51                 (u1_struct_0 @ X39))))
% 36.30/36.51          | ~ (v5_pre_topc @ X42 @ X41 @ X39)
% 36.30/36.51          | (v5_pre_topc @ X40 @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X39)
% 36.30/36.51          | ((X42) != (X40))
% 36.30/36.51          | ~ (m1_subset_1 @ X42 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 36.30/36.51          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 36.30/36.51          | ~ (v1_funct_1 @ X42)
% 36.30/36.51          | ~ (l1_pre_topc @ X41)
% 36.30/36.51          | ~ (v2_pre_topc @ X41))),
% 36.30/36.51      inference('cnf', [status(esa)], [t62_pre_topc])).
% 36.30/36.51  thf('13', plain,
% 36.30/36.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 36.30/36.51         (~ (v2_pre_topc @ X41)
% 36.30/36.51          | ~ (l1_pre_topc @ X41)
% 36.30/36.51          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 36.30/36.51          | ~ (m1_subset_1 @ X40 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 36.30/36.51          | (v5_pre_topc @ X40 @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X39)
% 36.30/36.51          | ~ (v5_pre_topc @ X40 @ X41 @ X39)
% 36.30/36.51          | ~ (m1_subset_1 @ X40 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ 
% 36.30/36.51                 (u1_struct_0 @ 
% 36.30/36.51                  (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.30/36.51                 (u1_struct_0 @ X39))))
% 36.30/36.51          | ~ (v1_funct_2 @ X40 @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.30/36.51               (u1_struct_0 @ X39))
% 36.30/36.51          | ~ (v1_funct_1 @ X40)
% 36.30/36.51          | ~ (l1_pre_topc @ X39)
% 36.30/36.51          | ~ (v2_pre_topc @ X39))),
% 36.30/36.51      inference('simplify', [status(thm)], ['12'])).
% 36.30/36.51  thf('14', plain,
% 36.30/36.51      ((~ (v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v1_funct_1 @ sk_C_2)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51             (k1_zfmisc_1 @ 
% 36.30/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (l1_pre_topc @ sk_A)
% 36.30/36.51        | ~ (v2_pre_topc @ sk_A))),
% 36.30/36.51      inference('sup-', [status(thm)], ['11', '13'])).
% 36.30/36.51  thf('15', plain, ((v1_funct_1 @ sk_C_2)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('18', plain,
% 36.30/36.51      ((~ (v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51             (k1_zfmisc_1 @ 
% 36.30/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 36.30/36.51  thf('19', plain,
% 36.30/36.51      ((v1_funct_2 @ sk_D @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('20', plain, (((sk_C_2) = (sk_D))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('21', plain,
% 36.30/36.51      ((v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('demod', [status(thm)], ['19', '20'])).
% 36.30/36.51  thf('22', plain,
% 36.30/36.51      ((~ (v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51             (k1_zfmisc_1 @ 
% 36.30/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['18', '21'])).
% 36.30/36.51  thf('23', plain,
% 36.30/36.51      ((~ (v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v2_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['8', '22'])).
% 36.30/36.51  thf('24', plain,
% 36.30/36.51      (![X38 : $i]:
% 36.30/36.51         ((v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 36.30/36.51          | ~ (l1_pre_topc @ X38)
% 36.30/36.51          | ~ (v2_pre_topc @ X38))),
% 36.30/36.51      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 36.30/36.51  thf('25', plain,
% 36.30/36.51      (![X0 : $i]:
% 36.30/36.51         (~ (l1_pre_topc @ X0)
% 36.30/36.51          | (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['0', '1'])).
% 36.30/36.51  thf('26', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_D @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('27', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))
% 36.30/36.51         <= (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))),
% 36.30/36.51      inference('split', [status(esa)], ['26'])).
% 36.30/36.51  thf('28', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('demod', [status(thm)], ['9', '10'])).
% 36.30/36.51  thf(cc5_funct_2, axiom,
% 36.30/36.51    (![A:$i,B:$i]:
% 36.30/36.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 36.30/36.51       ( ![C:$i]:
% 36.30/36.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.30/36.51           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 36.30/36.51             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 36.30/36.51  thf('29', plain,
% 36.30/36.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 36.30/36.51         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 36.30/36.51          | (v1_partfun1 @ X25 @ X26)
% 36.30/36.51          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 36.30/36.51          | ~ (v1_funct_1 @ X25)
% 36.30/36.51          | (v1_xboole_0 @ X27))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc5_funct_2])).
% 36.30/36.51  thf('30', plain,
% 36.30/36.51      (((v1_xboole_0 @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (v1_funct_1 @ sk_C_2)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_partfun1 @ sk_C_2 @ 
% 36.30/36.51           (u1_struct_0 @ 
% 36.30/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['28', '29'])).
% 36.30/36.51  thf('31', plain, ((v1_funct_1 @ sk_C_2)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('32', plain,
% 36.30/36.51      (((v1_xboole_0 @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_partfun1 @ sk_C_2 @ 
% 36.30/36.51           (u1_struct_0 @ 
% 36.30/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['30', '31'])).
% 36.30/36.51  thf('33', plain,
% 36.30/36.51      ((v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('demod', [status(thm)], ['19', '20'])).
% 36.30/36.51  thf('34', plain,
% 36.30/36.51      (((v1_xboole_0 @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_partfun1 @ sk_C_2 @ 
% 36.30/36.51           (u1_struct_0 @ 
% 36.30/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['32', '33'])).
% 36.30/36.51  thf(d4_partfun1, axiom,
% 36.30/36.51    (![A:$i,B:$i]:
% 36.30/36.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 36.30/36.51       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 36.30/36.51  thf('35', plain,
% 36.30/36.51      (![X31 : $i, X32 : $i]:
% 36.30/36.51         (~ (v1_partfun1 @ X32 @ X31)
% 36.30/36.51          | ((k1_relat_1 @ X32) = (X31))
% 36.30/36.51          | ~ (v4_relat_1 @ X32 @ X31)
% 36.30/36.51          | ~ (v1_relat_1 @ X32))),
% 36.30/36.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 36.30/36.51  thf('36', plain,
% 36.30/36.51      (((v1_xboole_0 @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (v1_relat_1 @ sk_C_2)
% 36.30/36.51        | ~ (v4_relat_1 @ sk_C_2 @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 36.30/36.51        | ((k1_relat_1 @ sk_C_2)
% 36.30/36.51            = (u1_struct_0 @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['34', '35'])).
% 36.30/36.51  thf('37', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf(cc2_relat_1, axiom,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( v1_relat_1 @ A ) =>
% 36.30/36.51       ( ![B:$i]:
% 36.30/36.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 36.30/36.51  thf('38', plain,
% 36.30/36.51      (![X14 : $i, X15 : $i]:
% 36.30/36.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 36.30/36.51          | (v1_relat_1 @ X14)
% 36.30/36.51          | ~ (v1_relat_1 @ X15))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 36.30/36.51  thf('39', plain,
% 36.30/36.51      ((~ (v1_relat_1 @ 
% 36.30/36.51           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 36.30/36.51        | (v1_relat_1 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['37', '38'])).
% 36.30/36.51  thf(fc6_relat_1, axiom,
% 36.30/36.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 36.30/36.51  thf('40', plain,
% 36.30/36.51      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 36.30/36.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 36.30/36.51  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 36.30/36.51      inference('demod', [status(thm)], ['39', '40'])).
% 36.30/36.51  thf('42', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('demod', [status(thm)], ['9', '10'])).
% 36.30/36.51  thf(cc2_relset_1, axiom,
% 36.30/36.51    (![A:$i,B:$i,C:$i]:
% 36.30/36.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.30/36.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 36.30/36.51  thf('43', plain,
% 36.30/36.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.30/36.51         ((v4_relat_1 @ X19 @ X20)
% 36.30/36.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 36.30/36.51  thf('44', plain,
% 36.30/36.51      ((v4_relat_1 @ sk_C_2 @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['42', '43'])).
% 36.30/36.51  thf('45', plain,
% 36.30/36.51      (((v1_xboole_0 @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ((k1_relat_1 @ sk_C_2)
% 36.30/36.51            = (u1_struct_0 @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['36', '41', '44'])).
% 36.30/36.51  thf('46', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('demod', [status(thm)], ['9', '10'])).
% 36.30/36.51  thf(cc4_relset_1, axiom,
% 36.30/36.51    (![A:$i,B:$i]:
% 36.30/36.51     ( ( v1_xboole_0 @ A ) =>
% 36.30/36.51       ( ![C:$i]:
% 36.30/36.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 36.30/36.51           ( v1_xboole_0 @ C ) ) ) ))).
% 36.30/36.51  thf('47', plain,
% 36.30/36.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 36.30/36.51         (~ (v1_xboole_0 @ X22)
% 36.30/36.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 36.30/36.51          | (v1_xboole_0 @ X23))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc4_relset_1])).
% 36.30/36.51  thf('48', plain,
% 36.30/36.51      (((v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | ~ (v1_xboole_0 @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['46', '47'])).
% 36.30/36.51  thf('49', plain,
% 36.30/36.51      ((((k1_relat_1 @ sk_C_2)
% 36.30/36.51          = (u1_struct_0 @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['45', '48'])).
% 36.30/36.51  thf('50', plain,
% 36.30/36.51      ((v1_funct_2 @ sk_C_2 @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51        (u1_struct_0 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('demod', [status(thm)], ['19', '20'])).
% 36.30/36.51  thf('51', plain,
% 36.30/36.51      (((v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup+', [status(thm)], ['49', '50'])).
% 36.30/36.51  thf('52', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('53', plain,
% 36.30/36.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 36.30/36.51         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 36.30/36.51          | (v1_partfun1 @ X25 @ X26)
% 36.30/36.51          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 36.30/36.51          | ~ (v1_funct_1 @ X25)
% 36.30/36.51          | (v1_xboole_0 @ X27))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc5_funct_2])).
% 36.30/36.51  thf('54', plain,
% 36.30/36.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.30/36.51        | ~ (v1_funct_1 @ sk_C_2)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ sk_B_1))
% 36.30/36.51        | (v1_partfun1 @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 36.30/36.51      inference('sup-', [status(thm)], ['52', '53'])).
% 36.30/36.51  thf('55', plain, ((v1_funct_1 @ sk_C_2)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('56', plain,
% 36.30/36.51      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('57', plain,
% 36.30/36.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.30/36.51        | (v1_partfun1 @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 36.30/36.51      inference('demod', [status(thm)], ['54', '55', '56'])).
% 36.30/36.51  thf('58', plain,
% 36.30/36.51      (![X31 : $i, X32 : $i]:
% 36.30/36.51         (~ (v1_partfun1 @ X32 @ X31)
% 36.30/36.51          | ((k1_relat_1 @ X32) = (X31))
% 36.30/36.51          | ~ (v4_relat_1 @ X32 @ X31)
% 36.30/36.51          | ~ (v1_relat_1 @ X32))),
% 36.30/36.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 36.30/36.51  thf('59', plain,
% 36.30/36.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.30/36.51        | ~ (v1_relat_1 @ sk_C_2)
% 36.30/36.51        | ~ (v4_relat_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))
% 36.30/36.51        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.30/36.51      inference('sup-', [status(thm)], ['57', '58'])).
% 36.30/36.51  thf('60', plain, ((v1_relat_1 @ sk_C_2)),
% 36.30/36.51      inference('demod', [status(thm)], ['39', '40'])).
% 36.30/36.51  thf('61', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('62', plain,
% 36.30/36.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 36.30/36.51         ((v4_relat_1 @ X19 @ X20)
% 36.30/36.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 36.30/36.51  thf('63', plain, ((v4_relat_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 36.30/36.51      inference('sup-', [status(thm)], ['61', '62'])).
% 36.30/36.51  thf('64', plain,
% 36.30/36.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.30/36.51        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.30/36.51      inference('demod', [status(thm)], ['59', '60', '63'])).
% 36.30/36.51  thf('65', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('66', plain,
% 36.30/36.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 36.30/36.51         (~ (v1_xboole_0 @ X22)
% 36.30/36.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 36.30/36.51          | (v1_xboole_0 @ X23))),
% 36.30/36.51      inference('cnf', [status(esa)], [cc4_relset_1])).
% 36.30/36.51  thf('67', plain,
% 36.30/36.51      (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 36.30/36.51      inference('sup-', [status(thm)], ['65', '66'])).
% 36.30/36.51  thf('68', plain,
% 36.30/36.51      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['64', '67'])).
% 36.30/36.51  thf('69', plain,
% 36.30/36.51      ((((k1_relat_1 @ sk_C_2)
% 36.30/36.51          = (u1_struct_0 @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['45', '48'])).
% 36.30/36.51  thf('70', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('demod', [status(thm)], ['9', '10'])).
% 36.30/36.51  thf('71', plain,
% 36.30/36.51      (((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51         (k1_zfmisc_1 @ 
% 36.30/36.51          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51           (u1_struct_0 @ 
% 36.30/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup+', [status(thm)], ['69', '70'])).
% 36.30/36.51  thf('72', plain,
% 36.30/36.51      (![X0 : $i, X1 : $i]:
% 36.30/36.51         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 36.30/36.51      inference('sup-', [status(thm)], ['6', '7'])).
% 36.30/36.51  thf('73', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('clc', [status(thm)], ['71', '72'])).
% 36.30/36.51  thf('74', plain,
% 36.30/36.51      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['64', '67'])).
% 36.30/36.51  thf(t63_pre_topc, axiom,
% 36.30/36.51    (![A:$i]:
% 36.30/36.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.30/36.51       ( ![B:$i]:
% 36.30/36.51         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 36.30/36.51           ( ![C:$i]:
% 36.30/36.51             ( ( ( v1_funct_1 @ C ) & 
% 36.30/36.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 36.30/36.51                 ( m1_subset_1 @
% 36.30/36.51                   C @ 
% 36.30/36.51                   ( k1_zfmisc_1 @
% 36.30/36.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 36.30/36.51               ( ![D:$i]:
% 36.30/36.51                 ( ( ( v1_funct_1 @ D ) & 
% 36.30/36.51                     ( v1_funct_2 @
% 36.30/36.51                       D @ ( u1_struct_0 @ A ) @ 
% 36.30/36.51                       ( u1_struct_0 @
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 36.30/36.51                     ( m1_subset_1 @
% 36.30/36.51                       D @ 
% 36.30/36.51                       ( k1_zfmisc_1 @
% 36.30/36.51                         ( k2_zfmisc_1 @
% 36.30/36.51                           ( u1_struct_0 @ A ) @ 
% 36.30/36.51                           ( u1_struct_0 @
% 36.30/36.51                             ( g1_pre_topc @
% 36.30/36.51                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 36.30/36.51                   ( ( ( C ) = ( D ) ) =>
% 36.30/36.51                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 36.30/36.51                       ( v5_pre_topc @
% 36.30/36.51                         D @ A @ 
% 36.30/36.51                         ( g1_pre_topc @
% 36.30/36.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 36.30/36.51  thf('75', plain,
% 36.30/36.51      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 36.30/36.51         (~ (v2_pre_topc @ X43)
% 36.30/36.51          | ~ (l1_pre_topc @ X43)
% 36.30/36.51          | ~ (v1_funct_1 @ X44)
% 36.30/36.51          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.30/36.51          | ~ (m1_subset_1 @ X44 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.30/36.51                 (u1_struct_0 @ 
% 36.30/36.51                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.30/36.51          | ~ (v5_pre_topc @ X46 @ X45 @ X43)
% 36.30/36.51          | (v5_pre_topc @ X44 @ X45 @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.30/36.51          | ((X46) != (X44))
% 36.30/36.51          | ~ (m1_subset_1 @ X46 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.30/36.51          | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.30/36.51          | ~ (v1_funct_1 @ X46)
% 36.30/36.51          | ~ (l1_pre_topc @ X45)
% 36.30/36.51          | ~ (v2_pre_topc @ X45))),
% 36.30/36.51      inference('cnf', [status(esa)], [t63_pre_topc])).
% 36.30/36.51  thf('76', plain,
% 36.30/36.51      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.30/36.51         (~ (v2_pre_topc @ X45)
% 36.30/36.51          | ~ (l1_pre_topc @ X45)
% 36.30/36.51          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.30/36.51          | ~ (m1_subset_1 @ X44 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.30/36.51          | (v5_pre_topc @ X44 @ X45 @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.30/36.51          | ~ (v5_pre_topc @ X44 @ X45 @ X43)
% 36.30/36.51          | ~ (m1_subset_1 @ X44 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.30/36.51                 (u1_struct_0 @ 
% 36.30/36.51                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.30/36.51          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.30/36.51          | ~ (v1_funct_1 @ X44)
% 36.30/36.51          | ~ (l1_pre_topc @ X43)
% 36.30/36.51          | ~ (v2_pre_topc @ X43))),
% 36.30/36.51      inference('simplify', [status(thm)], ['75'])).
% 36.30/36.51  thf('77', plain,
% 36.30/36.51      (![X0 : $i, X1 : $i]:
% 36.30/36.51         (~ (m1_subset_1 @ X1 @ 
% 36.30/36.51             (k1_zfmisc_1 @ 
% 36.30/36.51              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 36.30/36.51          | (v1_xboole_0 @ sk_C_2)
% 36.30/36.51          | ~ (v2_pre_topc @ X0)
% 36.30/36.51          | ~ (l1_pre_topc @ X0)
% 36.30/36.51          | ~ (v1_funct_1 @ X1)
% 36.30/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.30/36.51          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 36.30/36.51          | (v5_pre_topc @ X1 @ sk_A @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.30/36.51          | ~ (m1_subset_1 @ X1 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 36.30/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 36.30/36.51          | ~ (l1_pre_topc @ sk_A)
% 36.30/36.51          | ~ (v2_pre_topc @ sk_A))),
% 36.30/36.51      inference('sup-', [status(thm)], ['74', '76'])).
% 36.30/36.51  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('80', plain,
% 36.30/36.51      (![X0 : $i, X1 : $i]:
% 36.30/36.51         (~ (m1_subset_1 @ X1 @ 
% 36.30/36.51             (k1_zfmisc_1 @ 
% 36.30/36.51              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 36.30/36.51          | (v1_xboole_0 @ sk_C_2)
% 36.30/36.51          | ~ (v2_pre_topc @ X0)
% 36.30/36.51          | ~ (l1_pre_topc @ X0)
% 36.30/36.51          | ~ (v1_funct_1 @ X1)
% 36.30/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.30/36.51          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 36.30/36.51          | (v5_pre_topc @ X1 @ sk_A @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.30/36.51          | ~ (m1_subset_1 @ X1 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 36.30/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0)))),
% 36.30/36.51      inference('demod', [status(thm)], ['77', '78', '79'])).
% 36.30/36.51  thf('81', plain,
% 36.30/36.51      ((~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 36.30/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51             (k1_zfmisc_1 @ 
% 36.30/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | ~ (v1_funct_1 @ sk_C_2)
% 36.30/36.51        | ~ (l1_pre_topc @ sk_B_1)
% 36.30/36.51        | ~ (v2_pre_topc @ sk_B_1)
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['73', '80'])).
% 36.30/36.51  thf('82', plain,
% 36.30/36.51      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('83', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('84', plain, ((v1_funct_1 @ sk_C_2)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('86', plain, ((v2_pre_topc @ sk_B_1)),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('87', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('demod', [status(thm)], ['81', '82', '83', '84', '85', '86'])).
% 36.30/36.51  thf('88', plain,
% 36.30/36.51      ((~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51           (u1_struct_0 @ 
% 36.30/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['68', '87'])).
% 36.30/36.51  thf('89', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51             (u1_struct_0 @ 
% 36.30/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('simplify', [status(thm)], ['88'])).
% 36.30/36.51  thf('90', plain,
% 36.30/36.51      (((v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['51', '89'])).
% 36.30/36.51  thf('91', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('simplify', [status(thm)], ['90'])).
% 36.30/36.51  thf('92', plain,
% 36.30/36.51      ((((v1_xboole_0 @ sk_C_2)
% 36.30/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.30/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.30/36.51         <= (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))),
% 36.30/36.51      inference('sup-', [status(thm)], ['27', '91'])).
% 36.30/36.51  thf('93', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_D @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('94', plain, (((sk_C_2) = (sk_D))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('95', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('demod', [status(thm)], ['93', '94'])).
% 36.30/36.51  thf('96', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51         <= (((v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('split', [status(esa)], ['95'])).
% 36.30/36.51  thf('97', plain,
% 36.30/36.51      ((~ (v5_pre_topc @ sk_D @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('98', plain,
% 36.30/36.51      ((~ (v5_pre_topc @ sk_D @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51         <= (~
% 36.30/36.51             ((v5_pre_topc @ sk_D @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('split', [status(esa)], ['97'])).
% 36.30/36.51  thf('99', plain, (((sk_C_2) = (sk_D))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('100', plain,
% 36.30/36.51      ((~ (v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51         <= (~
% 36.30/36.51             ((v5_pre_topc @ sk_D @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['98', '99'])).
% 36.30/36.51  thf('101', plain,
% 36.30/36.51      (~
% 36.30/36.51       ((v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 36.30/36.51       ((v5_pre_topc @ sk_D @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['96', '100'])).
% 36.30/36.51  thf('102', plain,
% 36.30/36.51      ((~ (v5_pre_topc @ sk_D @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('103', plain, (((sk_C_2) = (sk_D))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('104', plain,
% 36.30/36.51      ((~ (v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.30/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('demod', [status(thm)], ['102', '103'])).
% 36.30/36.51  thf('105', plain,
% 36.30/36.51      (~
% 36.30/36.51       ((v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 36.30/36.51       ~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.30/36.51      inference('split', [status(esa)], ['104'])).
% 36.30/36.51  thf('106', plain,
% 36.30/36.51      (![X38 : $i]:
% 36.30/36.51         ((v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 36.30/36.51          | ~ (l1_pre_topc @ X38)
% 36.30/36.51          | ~ (v2_pre_topc @ X38))),
% 36.30/36.51      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 36.30/36.51  thf('107', plain,
% 36.30/36.51      (![X0 : $i]:
% 36.30/36.51         (~ (l1_pre_topc @ X0)
% 36.30/36.51          | (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['0', '1'])).
% 36.30/36.51  thf('108', plain,
% 36.30/36.51      (![X0 : $i]:
% 36.30/36.51         (~ (l1_pre_topc @ X0)
% 36.30/36.51          | (l1_pre_topc @ 
% 36.30/36.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 36.30/36.51      inference('sup-', [status(thm)], ['0', '1'])).
% 36.30/36.51  thf('109', plain,
% 36.30/36.51      (![X38 : $i]:
% 36.30/36.51         ((v2_pre_topc @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 36.30/36.51          | ~ (l1_pre_topc @ X38)
% 36.30/36.51          | ~ (v2_pre_topc @ X38))),
% 36.30/36.51      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 36.30/36.51  thf('110', plain,
% 36.30/36.51      (((v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.30/36.51         (u1_struct_0 @ 
% 36.30/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup+', [status(thm)], ['49', '50'])).
% 36.30/36.51  thf('111', plain,
% 36.30/36.51      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['64', '67'])).
% 36.30/36.51  thf('112', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_D @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('split', [status(esa)], ['26'])).
% 36.30/36.51  thf('113', plain, (((sk_C_2) = (sk_D))),
% 36.30/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.30/36.51  thf('114', plain,
% 36.30/36.51      (((v5_pre_topc @ sk_C_2 @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.30/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.30/36.51      inference('demod', [status(thm)], ['112', '113'])).
% 36.30/36.51  thf('115', plain,
% 36.30/36.51      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.30/36.51      inference('sup-', [status(thm)], ['64', '67'])).
% 36.30/36.51  thf('116', plain,
% 36.30/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.30/36.51        (k1_zfmisc_1 @ 
% 36.30/36.51         (k2_zfmisc_1 @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.30/36.51          (u1_struct_0 @ 
% 36.30/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.30/36.51      inference('demod', [status(thm)], ['9', '10'])).
% 36.30/36.51  thf('117', plain,
% 36.30/36.51      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 36.30/36.51         (~ (v2_pre_topc @ X39)
% 36.30/36.51          | ~ (l1_pre_topc @ X39)
% 36.30/36.51          | ~ (v1_funct_1 @ X40)
% 36.30/36.51          | ~ (v1_funct_2 @ X40 @ 
% 36.30/36.51               (u1_struct_0 @ 
% 36.30/36.51                (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.30/36.51               (u1_struct_0 @ X39))
% 36.30/36.51          | ~ (m1_subset_1 @ X40 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ 
% 36.30/36.51                 (u1_struct_0 @ 
% 36.30/36.51                  (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.30/36.51                 (u1_struct_0 @ X39))))
% 36.30/36.51          | ~ (v5_pre_topc @ X40 @ 
% 36.30/36.51               (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X39)
% 36.30/36.51          | (v5_pre_topc @ X42 @ X41 @ X39)
% 36.30/36.51          | ((X42) != (X40))
% 36.30/36.51          | ~ (m1_subset_1 @ X42 @ 
% 36.30/36.51               (k1_zfmisc_1 @ 
% 36.30/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 36.30/36.51          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 36.32/36.51          | ~ (v1_funct_1 @ X42)
% 36.32/36.51          | ~ (l1_pre_topc @ X41)
% 36.32/36.51          | ~ (v2_pre_topc @ X41))),
% 36.32/36.51      inference('cnf', [status(esa)], [t62_pre_topc])).
% 36.32/36.51  thf('118', plain,
% 36.32/36.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 36.32/36.51         (~ (v2_pre_topc @ X41)
% 36.32/36.51          | ~ (l1_pre_topc @ X41)
% 36.32/36.51          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 36.32/36.51          | ~ (m1_subset_1 @ X40 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 36.32/36.51          | (v5_pre_topc @ X40 @ X41 @ X39)
% 36.32/36.51          | ~ (v5_pre_topc @ X40 @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X39)
% 36.32/36.51          | ~ (m1_subset_1 @ X40 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ 
% 36.32/36.51                 (u1_struct_0 @ 
% 36.32/36.51                  (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.32/36.51                 (u1_struct_0 @ X39))))
% 36.32/36.51          | ~ (v1_funct_2 @ X40 @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.32/36.51               (u1_struct_0 @ X39))
% 36.32/36.51          | ~ (v1_funct_1 @ X40)
% 36.32/36.51          | ~ (l1_pre_topc @ X39)
% 36.32/36.51          | ~ (v2_pre_topc @ X39))),
% 36.32/36.51      inference('simplify', [status(thm)], ['117'])).
% 36.32/36.51  thf('119', plain,
% 36.32/36.51      ((~ (v2_pre_topc @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (l1_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v1_funct_1 @ sk_C_2)
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | ~ (l1_pre_topc @ sk_A)
% 36.32/36.51        | ~ (v2_pre_topc @ sk_A))),
% 36.32/36.51      inference('sup-', [status(thm)], ['116', '118'])).
% 36.32/36.51  thf('120', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('123', plain,
% 36.32/36.51      ((~ (v2_pre_topc @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (l1_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 36.32/36.51  thf('124', plain,
% 36.32/36.51      ((v1_funct_2 @ sk_C_2 @ 
% 36.32/36.51        (u1_struct_0 @ 
% 36.32/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.51        (u1_struct_0 @ 
% 36.32/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.51      inference('demod', [status(thm)], ['19', '20'])).
% 36.32/36.51  thf('125', plain,
% 36.32/36.51      ((~ (v2_pre_topc @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (l1_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['123', '124'])).
% 36.32/36.51  thf('126', plain,
% 36.32/36.51      ((~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51           (k1_zfmisc_1 @ 
% 36.32/36.51            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (l1_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v2_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['115', '125'])).
% 36.32/36.51  thf('127', plain,
% 36.32/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51        (k1_zfmisc_1 @ 
% 36.32/36.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51          (u1_struct_0 @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.32/36.51      inference('clc', [status(thm)], ['71', '72'])).
% 36.32/36.51  thf('128', plain,
% 36.32/36.51      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (l1_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v2_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.51      inference('demod', [status(thm)], ['126', '127'])).
% 36.32/36.51  thf('129', plain,
% 36.32/36.51      (((~ (v2_pre_topc @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51              (u1_struct_0 @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['114', '128'])).
% 36.32/36.51  thf('130', plain,
% 36.32/36.51      (((~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51            (u1_struct_0 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (v2_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['111', '129'])).
% 36.32/36.51  thf('131', plain,
% 36.32/36.51      (((~ (v2_pre_topc @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | ~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51              (u1_struct_0 @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('simplify', [status(thm)], ['130'])).
% 36.32/36.51  thf('132', plain,
% 36.32/36.51      ((((v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (v2_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['110', '131'])).
% 36.32/36.51  thf('133', plain,
% 36.32/36.51      (((~ (v2_pre_topc @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('simplify', [status(thm)], ['132'])).
% 36.32/36.51  thf('134', plain,
% 36.32/36.51      (((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.51         | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['109', '133'])).
% 36.32/36.51  thf('135', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('136', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('137', plain,
% 36.32/36.51      ((((v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['134', '135', '136'])).
% 36.32/36.51  thf('138', plain,
% 36.32/36.51      (((~ (l1_pre_topc @ sk_B_1)
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['108', '137'])).
% 36.32/36.51  thf('139', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('140', plain,
% 36.32/36.51      ((((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['138', '139'])).
% 36.32/36.51  thf('141', plain,
% 36.32/36.51      (((v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51         (u1_struct_0 @ 
% 36.32/36.51          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.51      inference('sup+', [status(thm)], ['49', '50'])).
% 36.32/36.51  thf('142', plain,
% 36.32/36.51      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.51      inference('sup-', [status(thm)], ['64', '67'])).
% 36.32/36.51  thf('143', plain,
% 36.32/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51        (k1_zfmisc_1 @ 
% 36.32/36.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51          (u1_struct_0 @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.32/36.51      inference('clc', [status(thm)], ['71', '72'])).
% 36.32/36.51  thf('144', plain,
% 36.32/36.51      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.51      inference('sup-', [status(thm)], ['64', '67'])).
% 36.32/36.51  thf('145', plain,
% 36.32/36.51      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 36.32/36.51         (~ (v2_pre_topc @ X43)
% 36.32/36.51          | ~ (l1_pre_topc @ X43)
% 36.32/36.51          | ~ (v1_funct_1 @ X44)
% 36.32/36.51          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.32/36.51          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.32/36.51                 (u1_struct_0 @ 
% 36.32/36.51                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.32/36.51          | ~ (v5_pre_topc @ X44 @ X45 @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.32/36.51          | (v5_pre_topc @ X46 @ X45 @ X43)
% 36.32/36.51          | ((X46) != (X44))
% 36.32/36.51          | ~ (m1_subset_1 @ X46 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.32/36.51          | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.32/36.51          | ~ (v1_funct_1 @ X46)
% 36.32/36.51          | ~ (l1_pre_topc @ X45)
% 36.32/36.51          | ~ (v2_pre_topc @ X45))),
% 36.32/36.51      inference('cnf', [status(esa)], [t63_pre_topc])).
% 36.32/36.51  thf('146', plain,
% 36.32/36.51      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.32/36.51         (~ (v2_pre_topc @ X45)
% 36.32/36.51          | ~ (l1_pre_topc @ X45)
% 36.32/36.51          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.32/36.51          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.32/36.51          | (v5_pre_topc @ X44 @ X45 @ X43)
% 36.32/36.51          | ~ (v5_pre_topc @ X44 @ X45 @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.32/36.51          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.32/36.51                 (u1_struct_0 @ 
% 36.32/36.51                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.32/36.51          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.32/36.51          | ~ (v1_funct_1 @ X44)
% 36.32/36.51          | ~ (l1_pre_topc @ X43)
% 36.32/36.51          | ~ (v2_pre_topc @ X43))),
% 36.32/36.51      inference('simplify', [status(thm)], ['145'])).
% 36.32/36.51  thf('147', plain,
% 36.32/36.51      (![X0 : $i, X1 : $i]:
% 36.32/36.51         (~ (m1_subset_1 @ X1 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 36.32/36.51          | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51          | ~ (v2_pre_topc @ X0)
% 36.32/36.51          | ~ (l1_pre_topc @ X0)
% 36.32/36.51          | ~ (v1_funct_1 @ X1)
% 36.32/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.32/36.51          | ~ (v5_pre_topc @ X1 @ sk_A @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.51          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 36.32/36.51          | ~ (m1_subset_1 @ X1 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 36.32/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 36.32/36.51          | ~ (l1_pre_topc @ sk_A)
% 36.32/36.51          | ~ (v2_pre_topc @ sk_A))),
% 36.32/36.51      inference('sup-', [status(thm)], ['144', '146'])).
% 36.32/36.51  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('150', plain,
% 36.32/36.51      (![X0 : $i, X1 : $i]:
% 36.32/36.51         (~ (m1_subset_1 @ X1 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 36.32/36.51          | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51          | ~ (v2_pre_topc @ X0)
% 36.32/36.51          | ~ (l1_pre_topc @ X0)
% 36.32/36.51          | ~ (v1_funct_1 @ X1)
% 36.32/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.32/36.51          | ~ (v5_pre_topc @ X1 @ sk_A @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.51          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 36.32/36.51          | ~ (m1_subset_1 @ X1 @ 
% 36.32/36.51               (k1_zfmisc_1 @ 
% 36.32/36.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 36.32/36.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0)))),
% 36.32/36.51      inference('demod', [status(thm)], ['147', '148', '149'])).
% 36.32/36.51  thf('151', plain,
% 36.32/36.51      ((~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 36.32/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | ~ (v1_funct_1 @ sk_C_2)
% 36.32/36.51        | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.51        | ~ (v2_pre_topc @ sk_B_1)
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.51      inference('sup-', [status(thm)], ['143', '150'])).
% 36.32/36.51  thf('152', plain,
% 36.32/36.51      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('153', plain,
% 36.32/36.51      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51        (k1_zfmisc_1 @ 
% 36.32/36.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('154', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('155', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('156', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.51  thf('157', plain,
% 36.32/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.51      inference('demod', [status(thm)],
% 36.32/36.51                ['151', '152', '153', '154', '155', '156'])).
% 36.32/36.51  thf('158', plain,
% 36.32/36.51      ((~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51           (u1_struct_0 @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.32/36.51      inference('sup-', [status(thm)], ['142', '157'])).
% 36.32/36.51  thf('159', plain,
% 36.32/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('simplify', [status(thm)], ['158'])).
% 36.32/36.51  thf('160', plain,
% 36.32/36.51      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.32/36.51      inference('sup-', [status(thm)], ['141', '159'])).
% 36.32/36.51  thf('161', plain,
% 36.32/36.51      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.51      inference('simplify', [status(thm)], ['160'])).
% 36.32/36.51  thf('162', plain,
% 36.32/36.51      ((((v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v1_xboole_0 @ sk_C_2)
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['140', '161'])).
% 36.32/36.51  thf('163', plain,
% 36.32/36.51      ((((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1) | (v1_xboole_0 @ sk_C_2)))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('simplify', [status(thm)], ['162'])).
% 36.32/36.51  thf('164', plain,
% 36.32/36.51      ((~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))),
% 36.32/36.51      inference('split', [status(esa)], ['97'])).
% 36.32/36.51  thf('165', plain,
% 36.32/36.51      (((v1_xboole_0 @ sk_C_2))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.51             ((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['163', '164'])).
% 36.32/36.51  thf(l13_xboole_0, axiom,
% 36.32/36.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 36.32/36.51  thf('166', plain,
% 36.32/36.51      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.51  thf('167', plain,
% 36.32/36.51      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.51             ((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 36.32/36.51  thf('168', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 36.32/36.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 36.32/36.51  thf('169', plain,
% 36.32/36.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 36.32/36.51      inference('sup-', [status(thm)], ['4', '5'])).
% 36.32/36.51  thf('170', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.32/36.51      inference('sup-', [status(thm)], ['168', '169'])).
% 36.32/36.51  thf('171', plain,
% 36.32/36.51      (![X11 : $i, X13 : $i]:
% 36.32/36.51         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 36.32/36.51      inference('cnf', [status(esa)], [t3_subset])).
% 36.32/36.51  thf('172', plain,
% 36.32/36.51      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.51      inference('sup-', [status(thm)], ['170', '171'])).
% 36.32/36.51  thf('173', plain,
% 36.32/36.51      ((![X0 : $i]: (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0)))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.51             ((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup+', [status(thm)], ['167', '172'])).
% 36.32/36.51  thf('174', plain,
% 36.32/36.51      ((~ (v2_pre_topc @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (l1_pre_topc @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.51             (k1_zfmisc_1 @ 
% 36.32/36.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51               (u1_struct_0 @ 
% 36.32/36.51                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.51        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51             (u1_struct_0 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['123', '124'])).
% 36.32/36.51  thf('175', plain,
% 36.32/36.51      (((~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51            (u1_struct_0 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (v2_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.51             ((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['173', '174'])).
% 36.32/36.51  thf('176', plain,
% 36.32/36.51      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['112', '113'])).
% 36.32/36.51  thf('177', plain,
% 36.32/36.51      (((~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.51            (u1_struct_0 @ 
% 36.32/36.51             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.51         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.51            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (l1_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.51         | ~ (v2_pre_topc @ 
% 36.32/36.51              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.51             ((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('demod', [status(thm)], ['175', '176'])).
% 36.32/36.51  thf('178', plain,
% 36.32/36.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.51        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.51      inference('demod', [status(thm)], ['59', '60', '63'])).
% 36.32/36.51  thf('179', plain,
% 36.32/36.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 36.32/36.51      inference('sup-', [status(thm)], ['4', '5'])).
% 36.32/36.51  thf('180', plain,
% 36.32/36.51      (![X0 : $i]:
% 36.32/36.51         (((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.51          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0))),
% 36.32/36.51      inference('sup-', [status(thm)], ['178', '179'])).
% 36.32/36.51  thf('181', plain,
% 36.32/36.51      (![X11 : $i, X13 : $i]:
% 36.32/36.51         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 36.32/36.51      inference('cnf', [status(esa)], [t3_subset])).
% 36.32/36.51  thf('182', plain,
% 36.32/36.51      (![X0 : $i]:
% 36.32/36.51         (((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.51          | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_zfmisc_1 @ X0)))),
% 36.32/36.51      inference('sup-', [status(thm)], ['180', '181'])).
% 36.32/36.51  thf('183', plain,
% 36.32/36.51      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.51         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.51             ((v5_pre_topc @ sk_D @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.51               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.51      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.51  thf(t113_zfmisc_1, axiom,
% 36.32/36.51    (![A:$i,B:$i]:
% 36.32/36.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 36.32/36.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 36.32/36.51  thf('184', plain,
% 36.32/36.51      (![X9 : $i, X10 : $i]:
% 36.32/36.51         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 36.32/36.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 36.32/36.51  thf('185', plain,
% 36.32/36.51      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.51      inference('simplify', [status(thm)], ['184'])).
% 36.32/36.51  thf('186', plain,
% 36.32/36.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 36.32/36.51         (~ (v1_xboole_0 @ X22)
% 36.32/36.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 36.32/36.52          | (v1_xboole_0 @ X23))),
% 36.32/36.52      inference('cnf', [status(esa)], [cc4_relset_1])).
% 36.32/36.52  thf('187', plain,
% 36.32/36.52      (![X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.32/36.52          | (v1_xboole_0 @ X1)
% 36.32/36.52          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['185', '186'])).
% 36.32/36.52  thf('188', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 36.32/36.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 36.32/36.52  thf('189', plain,
% 36.32/36.52      (![X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.32/36.52          | (v1_xboole_0 @ X1))),
% 36.32/36.52      inference('demod', [status(thm)], ['187', '188'])).
% 36.32/36.52  thf('190', plain,
% 36.32/36.52      ((![X0 : $i]:
% 36.32/36.52          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C_2)) | (v1_xboole_0 @ X0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['183', '189'])).
% 36.32/36.52  thf('191', plain,
% 36.32/36.52      (((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['182', '190'])).
% 36.32/36.52  thf('192', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('193', plain,
% 36.32/36.52      (![X9 : $i, X10 : $i]:
% 36.32/36.52         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 36.32/36.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 36.32/36.52  thf('194', plain,
% 36.32/36.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 36.32/36.52      inference('simplify', [status(thm)], ['193'])).
% 36.32/36.52  thf(rc1_funct_2, axiom,
% 36.32/36.52    (![A:$i,B:$i]:
% 36.32/36.52     ( ?[C:$i]:
% 36.32/36.52       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 36.32/36.52         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 36.32/36.52         ( v1_relat_1 @ C ) & 
% 36.32/36.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 36.32/36.52  thf('195', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]:
% 36.32/36.52         (m1_subset_1 @ (sk_C_1 @ X33 @ X34) @ 
% 36.32/36.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('196', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (m1_subset_1 @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 36.32/36.52          (k1_zfmisc_1 @ k1_xboole_0))),
% 36.32/36.52      inference('sup+', [status(thm)], ['194', '195'])).
% 36.32/36.52  thf('197', plain,
% 36.32/36.52      (![X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.32/36.52          | (v1_xboole_0 @ X1))),
% 36.32/36.52      inference('demod', [status(thm)], ['187', '188'])).
% 36.32/36.52  thf('198', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_C_1 @ X0 @ k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['196', '197'])).
% 36.32/36.52  thf('199', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('200', plain,
% 36.32/36.52      (![X0 : $i]: ((sk_C_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['198', '199'])).
% 36.32/36.52  thf('201', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]:
% 36.32/36.52         (m1_subset_1 @ (sk_C_1 @ X33 @ X34) @ 
% 36.32/36.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('202', plain,
% 36.32/36.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 36.32/36.52          | (v1_partfun1 @ X25 @ X26)
% 36.32/36.52          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 36.32/36.52          | ~ (v1_funct_1 @ X25)
% 36.32/36.52          | (v1_xboole_0 @ X27))),
% 36.32/36.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 36.32/36.52  thf('203', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_xboole_0 @ X0)
% 36.32/36.52          | ~ (v1_funct_1 @ (sk_C_1 @ X0 @ X1))
% 36.32/36.52          | ~ (v1_funct_2 @ (sk_C_1 @ X0 @ X1) @ X1 @ X0)
% 36.32/36.52          | (v1_partfun1 @ (sk_C_1 @ X0 @ X1) @ X1))),
% 36.32/36.52      inference('sup-', [status(thm)], ['201', '202'])).
% 36.32/36.52  thf('204', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_funct_1 @ (sk_C_1 @ X33 @ X34))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('205', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_funct_2 @ (sk_C_1 @ X33 @ X34) @ X34 @ X33)),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('206', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_xboole_0 @ X0) | (v1_partfun1 @ (sk_C_1 @ X0 @ X1) @ X1))),
% 36.32/36.52      inference('demod', [status(thm)], ['203', '204', '205'])).
% 36.32/36.52  thf('207', plain,
% 36.32/36.52      (![X31 : $i, X32 : $i]:
% 36.32/36.52         (~ (v1_partfun1 @ X32 @ X31)
% 36.32/36.52          | ((k1_relat_1 @ X32) = (X31))
% 36.32/36.52          | ~ (v4_relat_1 @ X32 @ X31)
% 36.32/36.52          | ~ (v1_relat_1 @ X32))),
% 36.32/36.52      inference('cnf', [status(esa)], [d4_partfun1])).
% 36.32/36.52  thf('208', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_xboole_0 @ X1)
% 36.32/36.52          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 36.32/36.52          | ~ (v4_relat_1 @ (sk_C_1 @ X1 @ X0) @ X0)
% 36.32/36.52          | ((k1_relat_1 @ (sk_C_1 @ X1 @ X0)) = (X0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['206', '207'])).
% 36.32/36.52  thf('209', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (sk_C_1 @ X33 @ X34))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('210', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v4_relat_1 @ (sk_C_1 @ X33 @ X34) @ X34)),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('211', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_xboole_0 @ X1) | ((k1_relat_1 @ (sk_C_1 @ X1 @ X0)) = (X0)))),
% 36.32/36.52      inference('demod', [status(thm)], ['208', '209', '210'])).
% 36.32/36.52  thf('212', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 36.32/36.52      inference('sup+', [status(thm)], ['200', '211'])).
% 36.32/36.52  thf('213', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('214', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['212', '213'])).
% 36.32/36.52  thf('215', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.52      inference('condensation', [status(thm)], ['214'])).
% 36.32/36.52  thf('216', plain,
% 36.32/36.52      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup+', [status(thm)], ['192', '215'])).
% 36.32/36.52  thf('217', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('218', plain,
% 36.32/36.52      ((((k1_relat_1 @ sk_C_2) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['216', '217'])).
% 36.32/36.52  thf('219', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['191', '218'])).
% 36.32/36.52  thf('220', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (~ (l1_pre_topc @ X0)
% 36.32/36.52          | (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['0', '1'])).
% 36.32/36.52  thf('221', plain,
% 36.32/36.52      (![X38 : $i]:
% 36.32/36.52         ((v2_pre_topc @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 36.32/36.52          | ~ (l1_pre_topc @ X38)
% 36.32/36.52          | ~ (v2_pre_topc @ X38))),
% 36.32/36.52      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 36.32/36.52  thf('222', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('223', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]:
% 36.32/36.52         (m1_subset_1 @ (sk_C_1 @ X33 @ X34) @ 
% 36.32/36.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('224', plain,
% 36.32/36.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 36.32/36.52         (~ (v1_xboole_0 @ X22)
% 36.32/36.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 36.32/36.52          | (v1_xboole_0 @ X23))),
% 36.32/36.52      inference('cnf', [status(esa)], [cc4_relset_1])).
% 36.32/36.52  thf('225', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_xboole_0 @ (sk_C_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['223', '224'])).
% 36.32/36.52  thf('226', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('227', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v1_xboole_0 @ X1) | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['225', '226'])).
% 36.32/36.52  thf('228', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_funct_2 @ (sk_C_1 @ X33 @ X34) @ X34 @ X33)),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('229', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 36.32/36.52      inference('sup+', [status(thm)], ['227', '228'])).
% 36.32/36.52  thf('230', plain,
% 36.32/36.52      ((![X0 : $i, X1 : $i]:
% 36.32/36.52          ((v1_funct_2 @ sk_C_2 @ X1 @ X0) | ~ (v1_xboole_0 @ X0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup+', [status(thm)], ['222', '229'])).
% 36.32/36.52  thf('231', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['112', '113'])).
% 36.32/36.52  thf('232', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['6', '7'])).
% 36.32/36.52  thf('233', plain,
% 36.32/36.52      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52        (k1_zfmisc_1 @ 
% 36.32/36.52         (k2_zfmisc_1 @ 
% 36.32/36.52          (u1_struct_0 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52          (u1_struct_0 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.32/36.52      inference('demod', [status(thm)], ['9', '10'])).
% 36.32/36.52  thf('234', plain,
% 36.32/36.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X45)
% 36.32/36.52          | ~ (l1_pre_topc @ X45)
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.32/36.52          | (v5_pre_topc @ X44 @ X45 @ X43)
% 36.32/36.52          | ~ (v5_pre_topc @ X44 @ X45 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.32/36.52          | ~ (v1_funct_1 @ X44)
% 36.32/36.52          | ~ (l1_pre_topc @ X43)
% 36.32/36.52          | ~ (v2_pre_topc @ X43))),
% 36.32/36.52      inference('simplify', [status(thm)], ['145'])).
% 36.32/36.52  thf('235', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (v1_funct_1 @ sk_C_2)
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['233', '234'])).
% 36.32/36.52  thf('236', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('237', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('238', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('239', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('demod', [status(thm)], ['235', '236', '237', '238'])).
% 36.32/36.52  thf('240', plain,
% 36.32/36.52      ((v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52        (u1_struct_0 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52        (u1_struct_0 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['19', '20'])).
% 36.32/36.52  thf('241', plain,
% 36.32/36.52      ((~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('demod', [status(thm)], ['239', '240'])).
% 36.32/36.52  thf('242', plain,
% 36.32/36.52      ((~ (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['232', '241'])).
% 36.32/36.52  thf('243', plain,
% 36.32/36.52      ((((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52         | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52              (u1_struct_0 @ sk_B_1))
% 36.32/36.52         | ~ (l1_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | ~ (v2_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | ~ (v1_xboole_0 @ sk_C_2)))
% 36.32/36.52         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['231', '242'])).
% 36.32/36.52  thf('244', plain,
% 36.32/36.52      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52         | ~ (v1_xboole_0 @ sk_C_2)
% 36.32/36.52         | ~ (v2_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | ~ (l1_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52            sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['230', '243'])).
% 36.32/36.52  thf('245', plain,
% 36.32/36.52      (((v1_xboole_0 @ sk_C_2))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['163', '164'])).
% 36.32/36.52  thf('246', plain,
% 36.32/36.52      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52         | ~ (v2_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | ~ (l1_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52            sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['244', '245'])).
% 36.32/36.52  thf('247', plain,
% 36.32/36.52      (((~ (v2_pre_topc @ sk_A)
% 36.32/36.52         | ~ (l1_pre_topc @ sk_A)
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52            sk_B_1)
% 36.32/36.52         | ~ (l1_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['221', '246'])).
% 36.32/36.52  thf('248', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('249', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('250', plain,
% 36.32/36.52      ((((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52         | ~ (l1_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52         | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['247', '248', '249'])).
% 36.32/36.52  thf('251', plain,
% 36.32/36.52      (((~ (l1_pre_topc @ sk_A)
% 36.32/36.52         | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52            sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['220', '250'])).
% 36.32/36.52  thf('252', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('253', plain,
% 36.32/36.52      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52            sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['251', '252'])).
% 36.32/36.52  thf('254', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52            sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['219', '253'])).
% 36.32/36.52  thf('255', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['191', '218'])).
% 36.32/36.52  thf('256', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('257', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['255', '256'])).
% 36.32/36.52  thf('258', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('259', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | ((u1_struct_0 @ sk_B_1) = (sk_C_2))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['257', '258'])).
% 36.32/36.52  thf('260', plain,
% 36.32/36.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['170', '171'])).
% 36.32/36.52  thf('261', plain,
% 36.32/36.52      (![X39 : $i, X40 : $i, X41 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X41)
% 36.32/36.52          | ~ (l1_pre_topc @ X41)
% 36.32/36.52          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 36.32/36.52          | ~ (m1_subset_1 @ X40 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 36.32/36.52          | (v5_pre_topc @ X40 @ X41 @ X39)
% 36.32/36.52          | ~ (v5_pre_topc @ X40 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X39)
% 36.32/36.52          | ~ (m1_subset_1 @ X40 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.32/36.52                 (u1_struct_0 @ X39))))
% 36.32/36.52          | ~ (v1_funct_2 @ X40 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.32/36.52               (u1_struct_0 @ X39))
% 36.32/36.52          | ~ (v1_funct_1 @ X40)
% 36.32/36.52          | ~ (l1_pre_topc @ X39)
% 36.32/36.52          | ~ (v2_pre_topc @ X39))),
% 36.32/36.52      inference('simplify', [status(thm)], ['117'])).
% 36.32/36.52  thf('262', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X0)
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v1_funct_1 @ k1_xboole_0)
% 36.32/36.52          | ~ (v1_funct_2 @ k1_xboole_0 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))) @ 
% 36.32/36.52               (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (v5_pre_topc @ k1_xboole_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X0)
% 36.32/36.52          | (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 36.32/36.52          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 36.32/36.52          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52               (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (l1_pre_topc @ X1)
% 36.32/36.52          | ~ (v2_pre_topc @ X1))),
% 36.32/36.52      inference('sup-', [status(thm)], ['260', '261'])).
% 36.32/36.52  thf('263', plain,
% 36.32/36.52      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.52      inference('simplify', [status(thm)], ['184'])).
% 36.32/36.52  thf('264', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]:
% 36.32/36.52         (m1_subset_1 @ (sk_C_1 @ X33 @ X34) @ 
% 36.32/36.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('265', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 36.32/36.52          (k1_zfmisc_1 @ k1_xboole_0))),
% 36.32/36.52      inference('sup+', [status(thm)], ['263', '264'])).
% 36.32/36.52  thf('266', plain,
% 36.32/36.52      (![X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.32/36.52          | (v1_xboole_0 @ X1))),
% 36.32/36.52      inference('demod', [status(thm)], ['187', '188'])).
% 36.32/36.52  thf('267', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['265', '266'])).
% 36.32/36.52  thf('268', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('269', plain,
% 36.32/36.52      (![X0 : $i]: ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['267', '268'])).
% 36.32/36.52  thf('270', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_funct_1 @ (sk_C_1 @ X33 @ X34))),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('271', plain, ((v1_funct_1 @ k1_xboole_0)),
% 36.32/36.52      inference('sup+', [status(thm)], ['269', '270'])).
% 36.32/36.52  thf('272', plain,
% 36.32/36.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['170', '171'])).
% 36.32/36.52  thf('273', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X0)
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v1_funct_2 @ k1_xboole_0 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))) @ 
% 36.32/36.52               (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (v5_pre_topc @ k1_xboole_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X0)
% 36.32/36.52          | (v5_pre_topc @ k1_xboole_0 @ X1 @ X0)
% 36.32/36.52          | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52               (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (l1_pre_topc @ X1)
% 36.32/36.52          | ~ (v2_pre_topc @ X1))),
% 36.32/36.52      inference('demod', [status(thm)], ['262', '271', '272'])).
% 36.32/36.52  thf('274', plain,
% 36.32/36.52      ((![X0 : $i]:
% 36.32/36.52          (~ (v1_funct_2 @ k1_xboole_0 @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 36.32/36.52              sk_C_2)
% 36.32/36.52           | ((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52           | ~ (v2_pre_topc @ X0)
% 36.32/36.52           | ~ (l1_pre_topc @ X0)
% 36.32/36.52           | ~ (v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 36.32/36.52                (u1_struct_0 @ sk_B_1))
% 36.32/36.52           | (v5_pre_topc @ k1_xboole_0 @ X0 @ sk_B_1)
% 36.32/36.52           | ~ (v5_pre_topc @ k1_xboole_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 36.32/36.52                sk_B_1)
% 36.32/36.52           | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52           | ~ (v2_pre_topc @ sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['259', '273'])).
% 36.32/36.52  thf('275', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('276', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('277', plain,
% 36.32/36.52      (![X0 : $i]: ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['267', '268'])).
% 36.32/36.52  thf('278', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_funct_2 @ (sk_C_1 @ X33 @ X34) @ X34 @ X33)),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('279', plain,
% 36.32/36.52      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 36.32/36.52      inference('sup+', [status(thm)], ['277', '278'])).
% 36.32/36.52  thf('280', plain,
% 36.32/36.52      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_C_2))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup+', [status(thm)], ['276', '279'])).
% 36.32/36.52  thf('281', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('282', plain,
% 36.32/36.52      ((![X0 : $i]: (v1_funct_2 @ sk_C_2 @ X0 @ sk_C_2))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['280', '281'])).
% 36.32/36.52  thf('283', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('284', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('285', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('286', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('287', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('288', plain,
% 36.32/36.52      ((![X0 : $i]:
% 36.32/36.52          (((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52           | ~ (v2_pre_topc @ X0)
% 36.32/36.52           | ~ (l1_pre_topc @ X0)
% 36.32/36.52           | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ X0) @ 
% 36.32/36.52                (u1_struct_0 @ sk_B_1))
% 36.32/36.52           | (v5_pre_topc @ sk_C_2 @ X0 @ sk_B_1)
% 36.32/36.52           | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 36.32/36.52                sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)],
% 36.32/36.52                ['274', '275', '282', '283', '284', '285', '286', '287'])).
% 36.32/36.52  thf('289', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.52         | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52              (u1_struct_0 @ sk_B_1))
% 36.32/36.52         | ~ (l1_pre_topc @ sk_A)
% 36.32/36.52         | ~ (v2_pre_topc @ sk_A)
% 36.32/36.52         | ((sk_C_2) = (u1_struct_0 @ sk_A))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['254', '288'])).
% 36.32/36.52  thf('290', plain,
% 36.32/36.52      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('291', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('292', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('293', plain,
% 36.32/36.52      (((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.52         | ((sk_C_2) = (u1_struct_0 @ sk_A))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['289', '290', '291', '292'])).
% 36.32/36.52  thf('294', plain,
% 36.32/36.52      ((((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.52         | ((sk_C_2) = (u1_struct_0 @ sk_A))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('simplify', [status(thm)], ['293'])).
% 36.32/36.52  thf('295', plain,
% 36.32/36.52      ((~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))),
% 36.32/36.52      inference('split', [status(esa)], ['97'])).
% 36.32/36.52  thf('296', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('297', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('298', plain,
% 36.32/36.52      (![X0 : $i]: ((sk_C_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['198', '199'])).
% 36.32/36.52  thf('299', plain,
% 36.32/36.52      (![X33 : $i, X34 : $i]: (v1_funct_2 @ (sk_C_1 @ X33 @ X34) @ X34 @ X33)),
% 36.32/36.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 36.32/36.52  thf('300', plain,
% 36.32/36.52      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 36.32/36.52      inference('sup+', [status(thm)], ['298', '299'])).
% 36.32/36.52  thf('301', plain,
% 36.32/36.52      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ sk_C_2 @ X0))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup+', [status(thm)], ['297', '300'])).
% 36.32/36.52  thf('302', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('303', plain,
% 36.32/36.52      ((![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['301', '302'])).
% 36.32/36.52  thf('304', plain,
% 36.32/36.52      ((((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52         | ~ (l1_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52         | ~ (v2_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['177', '296', '303'])).
% 36.32/36.52  thf('305', plain,
% 36.32/36.52      (((~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52         | ~ (v2_pre_topc @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['107', '304'])).
% 36.32/36.52  thf('306', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('307', plain,
% 36.32/36.52      (((~ (v2_pre_topc @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['305', '306'])).
% 36.32/36.52  thf('308', plain,
% 36.32/36.52      (((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52         | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['106', '307'])).
% 36.32/36.52  thf('309', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('310', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('311', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['308', '309', '310'])).
% 36.32/36.52  thf('312', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('313', plain,
% 36.32/36.52      (![X4 : $i, X6 : $i]:
% 36.32/36.52         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 36.32/36.52      inference('cnf', [status(esa)], [d3_tarski])).
% 36.32/36.52  thf('314', plain,
% 36.32/36.52      (![X4 : $i, X6 : $i]:
% 36.32/36.52         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 36.32/36.52      inference('cnf', [status(esa)], [d3_tarski])).
% 36.32/36.52  thf('315', plain,
% 36.32/36.52      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['313', '314'])).
% 36.32/36.52  thf('316', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 36.32/36.52      inference('simplify', [status(thm)], ['315'])).
% 36.32/36.52  thf('317', plain,
% 36.32/36.52      (![X11 : $i, X13 : $i]:
% 36.32/36.52         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 36.32/36.52      inference('cnf', [status(esa)], [t3_subset])).
% 36.32/36.52  thf('318', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['316', '317'])).
% 36.32/36.52  thf('319', plain,
% 36.32/36.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X45)
% 36.32/36.52          | ~ (l1_pre_topc @ X45)
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.32/36.52          | (v5_pre_topc @ X44 @ X45 @ X43)
% 36.32/36.52          | ~ (v5_pre_topc @ X44 @ X45 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.32/36.52          | ~ (v1_funct_1 @ X44)
% 36.32/36.52          | ~ (l1_pre_topc @ X43)
% 36.32/36.52          | ~ (v2_pre_topc @ X43))),
% 36.32/36.52      inference('simplify', [status(thm)], ['145'])).
% 36.32/36.52  thf('320', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X0)
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v1_funct_1 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 36.32/36.52          | ~ (v1_funct_2 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (u1_struct_0 @ X1) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.32/36.52          | ~ (v5_pre_topc @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               X1 @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.52          | (v5_pre_topc @ 
% 36.32/36.52             (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52             X1 @ X0)
% 36.32/36.52          | ~ (m1_subset_1 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 36.32/36.52          | ~ (v1_funct_2 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (l1_pre_topc @ X1)
% 36.32/36.52          | ~ (v2_pre_topc @ X1))),
% 36.32/36.52      inference('sup-', [status(thm)], ['318', '319'])).
% 36.32/36.52  thf('321', plain,
% 36.32/36.52      ((![X0 : $i]:
% 36.32/36.52          (~ (v1_funct_2 @ 
% 36.32/36.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52              sk_C_2 @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.32/36.52           | ~ (v2_pre_topc @ sk_A)
% 36.32/36.52           | ~ (l1_pre_topc @ sk_A)
% 36.32/36.52           | ~ (v1_funct_2 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 36.32/36.52           | ~ (m1_subset_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52                (k1_zfmisc_1 @ 
% 36.32/36.52                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 36.32/36.52           | (v5_pre_topc @ 
% 36.32/36.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52              sk_A @ X0)
% 36.32/36.52           | ~ (v5_pre_topc @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52                sk_A @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.52           | ~ (v1_funct_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 36.32/36.52           | ~ (l1_pre_topc @ X0)
% 36.32/36.52           | ~ (v2_pre_topc @ X0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['312', '320'])).
% 36.32/36.52  thf('322', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('323', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('324', plain,
% 36.32/36.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 36.32/36.52      inference('simplify', [status(thm)], ['193'])).
% 36.32/36.52  thf('325', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup+', [status(thm)], ['323', '324'])).
% 36.32/36.52  thf('326', plain,
% 36.32/36.52      ((((sk_C_2) = (k1_xboole_0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['165', '166'])).
% 36.32/36.52  thf('327', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('328', plain,
% 36.32/36.52      ((![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['301', '302'])).
% 36.32/36.52  thf('329', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('330', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('331', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('332', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('333', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('334', plain,
% 36.32/36.52      ((![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['301', '302'])).
% 36.32/36.52  thf('335', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('336', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('337', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('338', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('339', plain,
% 36.32/36.52      ((![X0 : $i]: (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup+', [status(thm)], ['167', '172'])).
% 36.32/36.52  thf('340', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('341', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('342', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('343', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('344', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('clc', [status(thm)], ['294', '295'])).
% 36.32/36.52  thf('345', plain,
% 36.32/36.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X0) = (sk_C_2)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['325', '326'])).
% 36.32/36.52  thf('346', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('347', plain,
% 36.32/36.52      ((![X0 : $i]:
% 36.32/36.52          ((v5_pre_topc @ sk_C_2 @ sk_A @ X0)
% 36.32/36.52           | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.52           | ~ (l1_pre_topc @ X0)
% 36.32/36.52           | ~ (v2_pre_topc @ X0)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)],
% 36.32/36.52                ['321', '322', '327', '328', '329', '330', '331', '332', 
% 36.32/36.52                 '333', '334', '335', '336', '337', '338', '339', '340', 
% 36.32/36.52                 '341', '342', '343', '344', '345', '346'])).
% 36.32/36.52  thf('348', plain,
% 36.32/36.52      (((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52         | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52         | (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['311', '347'])).
% 36.32/36.52  thf('349', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('350', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('351', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) & 
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['348', '349', '350'])).
% 36.32/36.52  thf('352', plain,
% 36.32/36.52      ((~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))
% 36.32/36.52         <= (~ ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))),
% 36.32/36.52      inference('split', [status(esa)], ['97'])).
% 36.32/36.52  thf('353', plain,
% 36.32/36.52      (~
% 36.32/36.52       ((v5_pre_topc @ sk_D @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 36.32/36.52       ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.32/36.52      inference('sup-', [status(thm)], ['351', '352'])).
% 36.32/36.52  thf('354', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)) | 
% 36.32/36.52       ((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('split', [status(esa)], ['95'])).
% 36.32/36.52  thf('355', plain, (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.32/36.52      inference('sat_resolution*', [status(thm)], ['101', '105', '353', '354'])).
% 36.32/36.52  thf('356', plain,
% 36.32/36.52      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('simpl_trail', [status(thm)], ['92', '355'])).
% 36.32/36.52  thf('357', plain,
% 36.32/36.52      (((v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.52         (u1_struct_0 @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('sup+', [status(thm)], ['49', '50'])).
% 36.32/36.52  thf('358', plain,
% 36.32/36.52      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('sup-', [status(thm)], ['64', '67'])).
% 36.32/36.52  thf('359', plain,
% 36.32/36.52      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('sup-', [status(thm)], ['64', '67'])).
% 36.32/36.52  thf('360', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['18', '21'])).
% 36.32/36.52  thf('361', plain,
% 36.32/36.52      ((~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52           (k1_zfmisc_1 @ 
% 36.32/36.52            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['359', '360'])).
% 36.32/36.52  thf('362', plain,
% 36.32/36.52      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52        (k1_zfmisc_1 @ 
% 36.32/36.52         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.52          (u1_struct_0 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.32/36.52      inference('clc', [status(thm)], ['71', '72'])).
% 36.32/36.52  thf('363', plain,
% 36.32/36.52      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['361', '362'])).
% 36.32/36.52  thf('364', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('sup-', [status(thm)], ['358', '363'])).
% 36.32/36.52  thf('365', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('simplify', [status(thm)], ['364'])).
% 36.32/36.52  thf('366', plain,
% 36.32/36.52      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['357', '365'])).
% 36.32/36.52  thf('367', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('simplify', [status(thm)], ['366'])).
% 36.32/36.52  thf('368', plain,
% 36.32/36.52      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['356', '367'])).
% 36.32/36.52  thf('369', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('simplify', [status(thm)], ['368'])).
% 36.32/36.52  thf('370', plain,
% 36.32/36.52      ((~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['25', '369'])).
% 36.32/36.52  thf('371', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('372', plain,
% 36.32/36.52      (((v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['370', '371'])).
% 36.32/36.52  thf('373', plain,
% 36.32/36.52      ((~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52         <= (~
% 36.32/36.52             ((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['98', '99'])).
% 36.32/36.52  thf('374', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52         <= (((v5_pre_topc @ sk_D @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('demod', [status(thm)], ['112', '113'])).
% 36.32/36.52  thf('375', plain,
% 36.32/36.52      ((~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52         <= (~
% 36.32/36.52             ((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 36.32/36.52      inference('split', [status(esa)], ['104'])).
% 36.32/36.52  thf('376', plain,
% 36.32/36.52      (~
% 36.32/36.52       ((v5_pre_topc @ sk_D @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 36.32/36.52       ((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['374', '375'])).
% 36.32/36.52  thf('377', plain,
% 36.32/36.52      (~
% 36.32/36.52       ((v5_pre_topc @ sk_D @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sat_resolution*', [status(thm)], ['101', '105', '353', '376'])).
% 36.32/36.52  thf('378', plain,
% 36.32/36.52      (~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 36.32/36.52      inference('simpl_trail', [status(thm)], ['373', '377'])).
% 36.32/36.52  thf('379', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('clc', [status(thm)], ['372', '378'])).
% 36.32/36.52  thf('380', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52        | (v1_xboole_0 @ sk_C_2))),
% 36.32/36.52      inference('sup-', [status(thm)], ['24', '379'])).
% 36.32/36.52  thf('381', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('382', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('383', plain, ((v1_xboole_0 @ sk_C_2)),
% 36.32/36.52      inference('demod', [status(thm)], ['380', '381', '382'])).
% 36.32/36.52  thf('384', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['23', '383'])).
% 36.32/36.52  thf('385', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (~ (l1_pre_topc @ X0)
% 36.32/36.52          | (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['0', '1'])).
% 36.32/36.52  thf('386', plain,
% 36.32/36.52      (![X38 : $i]:
% 36.32/36.52         ((v2_pre_topc @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 36.32/36.52          | ~ (l1_pre_topc @ X38)
% 36.32/36.52          | ~ (v2_pre_topc @ X38))),
% 36.32/36.52      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 36.32/36.52  thf('387', plain,
% 36.32/36.52      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52        (k1_zfmisc_1 @ 
% 36.32/36.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('388', plain,
% 36.32/36.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.52      inference('demod', [status(thm)], ['59', '60', '63'])).
% 36.32/36.52  thf('389', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('390', plain,
% 36.32/36.52      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['388', '389'])).
% 36.32/36.52  thf('391', plain,
% 36.32/36.52      ((((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['388', '389'])).
% 36.32/36.52  thf('392', plain,
% 36.32/36.52      (![X39 : $i, X40 : $i, X41 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X41)
% 36.32/36.52          | ~ (l1_pre_topc @ X41)
% 36.32/36.52          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 36.32/36.52          | ~ (m1_subset_1 @ X40 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 36.32/36.52          | (v5_pre_topc @ X40 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X39)
% 36.32/36.52          | ~ (v5_pre_topc @ X40 @ X41 @ X39)
% 36.32/36.52          | ~ (m1_subset_1 @ X40 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.32/36.52                 (u1_struct_0 @ X39))))
% 36.32/36.52          | ~ (v1_funct_2 @ X40 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))) @ 
% 36.32/36.52               (u1_struct_0 @ X39))
% 36.32/36.52          | ~ (v1_funct_1 @ X40)
% 36.32/36.52          | ~ (l1_pre_topc @ X39)
% 36.32/36.52          | ~ (v2_pre_topc @ X39))),
% 36.32/36.52      inference('simplify', [status(thm)], ['12'])).
% 36.32/36.52  thf('393', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 36.32/36.52               k1_xboole_0)))
% 36.32/36.52          | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52          | ~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52          | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52          | ~ (v1_funct_1 @ X1)
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))
% 36.32/36.52          | ~ (v5_pre_topc @ X1 @ X0 @ sk_B_1)
% 36.32/36.52          | (v5_pre_topc @ X1 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 36.32/36.52          | ~ (m1_subset_1 @ X1 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v2_pre_topc @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['391', '392'])).
% 36.32/36.52  thf('394', plain,
% 36.32/36.52      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.52      inference('simplify', [status(thm)], ['184'])).
% 36.32/36.52  thf('395', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('396', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('397', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.32/36.52          | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52          | ~ (v1_funct_1 @ X1)
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))
% 36.32/36.52          | ~ (v5_pre_topc @ X1 @ X0 @ sk_B_1)
% 36.32/36.52          | (v5_pre_topc @ X1 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 36.32/36.52          | ~ (m1_subset_1 @ X1 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v2_pre_topc @ X0))),
% 36.32/36.52      inference('demod', [status(thm)], ['393', '394', '395', '396'])).
% 36.32/36.52  thf('398', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v1_funct_2 @ X1 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 36.32/36.52             k1_xboole_0)
% 36.32/36.52          | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52          | ~ (v2_pre_topc @ X0)
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52          | ~ (m1_subset_1 @ X1 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52          | (v5_pre_topc @ X1 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 36.32/36.52          | ~ (v5_pre_topc @ X1 @ X0 @ sk_B_1)
% 36.32/36.52          | ~ (v1_funct_1 @ X1)
% 36.32/36.52          | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['390', '397'])).
% 36.32/36.52  thf('399', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 36.32/36.52          | ~ (v1_funct_1 @ X1)
% 36.32/36.52          | ~ (v5_pre_topc @ X1 @ X0 @ sk_B_1)
% 36.32/36.52          | (v5_pre_topc @ X1 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ sk_B_1)
% 36.32/36.52          | ~ (m1_subset_1 @ X1 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v2_pre_topc @ X0)
% 36.32/36.52          | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52          | ~ (v1_funct_2 @ X1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 36.32/36.52               k1_xboole_0))),
% 36.32/36.52      inference('simplify', [status(thm)], ['398'])).
% 36.32/36.52  thf('400', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52           k1_xboole_0)
% 36.32/36.52        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | ~ (v2_pre_topc @ sk_A)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_A)
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 36.32/36.52        | ~ (v1_funct_1 @ sk_C_2)
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['387', '399'])).
% 36.32/36.52  thf('401', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('402', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('403', plain,
% 36.32/36.52      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('404', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))
% 36.32/36.52         <= (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)))),
% 36.32/36.52      inference('split', [status(esa)], ['26'])).
% 36.32/36.52  thf('405', plain, (((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1))),
% 36.32/36.52      inference('sat_resolution*', [status(thm)], ['101', '105', '353', '354'])).
% 36.32/36.52  thf('406', plain, ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)),
% 36.32/36.52      inference('simpl_trail', [status(thm)], ['404', '405'])).
% 36.32/36.52  thf('407', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('408', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52           k1_xboole_0)
% 36.32/36.52        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 36.32/36.52      inference('demod', [status(thm)],
% 36.32/36.52                ['400', '401', '402', '403', '406', '407'])).
% 36.32/36.52  thf('409', plain, ((v1_xboole_0 @ sk_C_2)),
% 36.32/36.52      inference('demod', [status(thm)], ['380', '381', '382'])).
% 36.32/36.52  thf('410', plain,
% 36.32/36.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 36.32/36.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 36.32/36.52  thf('411', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('412', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('413', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['316', '317'])).
% 36.32/36.52  thf('414', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52           sk_C_2)
% 36.32/36.52        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1))),
% 36.32/36.52      inference('demod', [status(thm)], ['408', '411', '412', '413'])).
% 36.32/36.52  thf('415', plain,
% 36.32/36.52      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 36.32/36.52      inference('sup+', [status(thm)], ['277', '278'])).
% 36.32/36.52  thf('416', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('417', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('418', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_2 @ X0 @ sk_C_2)),
% 36.32/36.52      inference('demod', [status(thm)], ['415', '416', '417'])).
% 36.32/36.52  thf('419', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 36.32/36.52      inference('condensation', [status(thm)], ['214'])).
% 36.32/36.52  thf('420', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('421', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('422', plain, (((k1_relat_1 @ sk_C_2) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['419', '420', '421'])).
% 36.32/36.52  thf('423', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1))),
% 36.32/36.52      inference('demod', [status(thm)], ['414', '418', '422'])).
% 36.32/36.52  thf('424', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 36.32/36.52      inference('sup+', [status(thm)], ['227', '228'])).
% 36.32/36.52  thf('425', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('426', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         ((v1_funct_2 @ sk_C_2 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 36.32/36.52      inference('demod', [status(thm)], ['424', '425'])).
% 36.32/36.52  thf('427', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['6', '7'])).
% 36.32/36.52  thf('428', plain,
% 36.32/36.52      ((m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52        (k1_zfmisc_1 @ 
% 36.32/36.52         (k2_zfmisc_1 @ 
% 36.32/36.52          (u1_struct_0 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52          (u1_struct_0 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 36.32/36.52      inference('demod', [status(thm)], ['9', '10'])).
% 36.32/36.52  thf('429', plain,
% 36.32/36.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X45)
% 36.32/36.52          | ~ (l1_pre_topc @ X45)
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.32/36.52          | (v5_pre_topc @ X44 @ X45 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.32/36.52          | ~ (v5_pre_topc @ X44 @ X45 @ X43)
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.32/36.52          | ~ (v1_funct_1 @ X44)
% 36.32/36.52          | ~ (l1_pre_topc @ X43)
% 36.32/36.52          | ~ (v2_pre_topc @ X43))),
% 36.32/36.52      inference('simplify', [status(thm)], ['75'])).
% 36.32/36.52  thf('430', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (v1_funct_1 @ sk_C_2)
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             sk_B_1)
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['428', '429'])).
% 36.32/36.52  thf('431', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('432', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('433', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('434', plain,
% 36.32/36.52      ((~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52           (u1_struct_0 @ 
% 36.32/36.52            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             sk_B_1)
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('demod', [status(thm)], ['430', '431', '432', '433'])).
% 36.32/36.52  thf('435', plain,
% 36.32/36.52      ((v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52        (u1_struct_0 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52        (u1_struct_0 @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['19', '20'])).
% 36.32/36.52  thf('436', plain,
% 36.32/36.52      ((~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (m1_subset_1 @ sk_C_2 @ 
% 36.32/36.52             (k1_zfmisc_1 @ 
% 36.32/36.52              (k2_zfmisc_1 @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_B_1))))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('demod', [status(thm)], ['434', '435'])).
% 36.32/36.52  thf('437', plain,
% 36.32/36.52      ((~ (v1_xboole_0 @ sk_C_2)
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             sk_B_1))),
% 36.32/36.52      inference('sup-', [status(thm)], ['427', '436'])).
% 36.32/36.52  thf('438', plain, ((v1_xboole_0 @ sk_C_2)),
% 36.32/36.52      inference('demod', [status(thm)], ['380', '381', '382'])).
% 36.32/36.52  thf('439', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v1_funct_2 @ sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 36.32/36.52             (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             sk_B_1))),
% 36.32/36.52      inference('demod', [status(thm)], ['437', '438'])).
% 36.32/36.52  thf('440', plain,
% 36.32/36.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52             sk_B_1)
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['426', '439'])).
% 36.32/36.52  thf('441', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['423', '440'])).
% 36.32/36.52  thf('442', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ sk_A)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_A)
% 36.32/36.52        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ((sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['386', '441'])).
% 36.32/36.52  thf('443', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('444', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('445', plain,
% 36.32/36.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 36.32/36.52        | ((sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.52      inference('demod', [status(thm)], ['442', '443', '444'])).
% 36.32/36.52  thf('446', plain,
% 36.32/36.52      ((~ (l1_pre_topc @ sk_A)
% 36.32/36.52        | ((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 36.32/36.52      inference('sup-', [status(thm)], ['385', '445'])).
% 36.32/36.52  thf('447', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('448', plain,
% 36.32/36.52      ((((sk_C_2) = (u1_struct_0 @ sk_A))
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 36.32/36.52      inference('demod', [status(thm)], ['446', '447'])).
% 36.32/36.52  thf('449', plain,
% 36.32/36.52      (~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 36.32/36.52      inference('simpl_trail', [status(thm)], ['373', '377'])).
% 36.32/36.52  thf('450', plain,
% 36.32/36.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ((sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.52      inference('clc', [status(thm)], ['448', '449'])).
% 36.32/36.52  thf('451', plain,
% 36.32/36.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ((k1_relat_1 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.52      inference('demod', [status(thm)], ['59', '60', '63'])).
% 36.32/36.52  thf('452', plain, (((k1_relat_1 @ sk_C_2) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['419', '420', '421'])).
% 36.32/36.52  thf('453', plain,
% 36.32/36.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 36.32/36.52        | ((sk_C_2) = (u1_struct_0 @ sk_A)))),
% 36.32/36.52      inference('demod', [status(thm)], ['451', '452'])).
% 36.32/36.52  thf('454', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('455', plain,
% 36.32/36.52      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 36.32/36.52      inference('sup+', [status(thm)], ['298', '299'])).
% 36.32/36.52  thf('456', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('457', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('458', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0)),
% 36.32/36.52      inference('demod', [status(thm)], ['455', '456', '457'])).
% 36.32/36.52  thf('459', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('460', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ sk_C_2 @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['384', '454', '458', '459'])).
% 36.32/36.52  thf('461', plain, ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)),
% 36.32/36.52      inference('simpl_trail', [status(thm)], ['404', '405'])).
% 36.32/36.52  thf('462', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('463', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['316', '317'])).
% 36.32/36.52  thf('464', plain,
% 36.32/36.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X45)
% 36.32/36.52          | ~ (l1_pre_topc @ X45)
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 36.32/36.52          | (v5_pre_topc @ X44 @ X45 @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 36.32/36.52          | ~ (v5_pre_topc @ X44 @ X45 @ X43)
% 36.32/36.52          | ~ (m1_subset_1 @ X44 @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52                 (u1_struct_0 @ 
% 36.32/36.52                  (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))))
% 36.32/36.52          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))
% 36.32/36.52          | ~ (v1_funct_1 @ X44)
% 36.32/36.52          | ~ (l1_pre_topc @ X43)
% 36.32/36.52          | ~ (v2_pre_topc @ X43))),
% 36.32/36.52      inference('simplify', [status(thm)], ['75'])).
% 36.32/36.52  thf('465', plain,
% 36.32/36.52      (![X0 : $i, X1 : $i]:
% 36.32/36.52         (~ (v2_pre_topc @ X0)
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v1_funct_1 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 36.32/36.52          | ~ (v1_funct_2 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (u1_struct_0 @ X1) @ 
% 36.32/36.52               (u1_struct_0 @ 
% 36.32/36.52                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.32/36.52          | ~ (v5_pre_topc @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               X1 @ X0)
% 36.32/36.52          | (v5_pre_topc @ 
% 36.32/36.52             (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52             X1 @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.52          | ~ (m1_subset_1 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 36.32/36.52          | ~ (v1_funct_2 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (l1_pre_topc @ X1)
% 36.32/36.52          | ~ (v2_pre_topc @ X1))),
% 36.32/36.52      inference('sup-', [status(thm)], ['463', '464'])).
% 36.32/36.52  thf('466', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         (~ (v1_funct_2 @ 
% 36.32/36.52             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52             sk_C_2 @ 
% 36.32/36.52             (u1_struct_0 @ 
% 36.32/36.52              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 36.32/36.52          | ~ (v2_pre_topc @ sk_A)
% 36.32/36.52          | ~ (l1_pre_topc @ sk_A)
% 36.32/36.52          | ~ (v1_funct_2 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 36.32/36.52          | ~ (m1_subset_1 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               (k1_zfmisc_1 @ 
% 36.32/36.52                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 36.32/36.52          | (v5_pre_topc @ 
% 36.32/36.52             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52              (u1_struct_0 @ 
% 36.32/36.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52             sk_A @ (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.52          | ~ (v5_pre_topc @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 36.32/36.52               sk_A @ X0)
% 36.32/36.52          | ~ (v1_funct_1 @ 
% 36.32/36.52               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 36.32/36.52                (u1_struct_0 @ 
% 36.32/36.52                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v2_pre_topc @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['462', '465'])).
% 36.32/36.52  thf('467', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('468', plain,
% 36.32/36.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 36.32/36.52      inference('simplify', [status(thm)], ['193'])).
% 36.32/36.52  thf('469', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('470', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('471', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('472', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0)),
% 36.32/36.52      inference('demod', [status(thm)], ['455', '456', '457'])).
% 36.32/36.52  thf('473', plain, ((v2_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('474', plain, ((l1_pre_topc @ sk_A)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('475', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('476', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('477', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('478', plain, (![X0 : $i]: (v1_funct_2 @ sk_C_2 @ sk_C_2 @ X0)),
% 36.32/36.52      inference('demod', [status(thm)], ['455', '456', '457'])).
% 36.32/36.52  thf('479', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('480', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('481', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('482', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('483', plain,
% 36.32/36.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['170', '171'])).
% 36.32/36.52  thf('484', plain, (((sk_C_2) = (k1_xboole_0))),
% 36.32/36.52      inference('sup-', [status(thm)], ['409', '410'])).
% 36.32/36.52  thf('485', plain, (![X0 : $i]: (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))),
% 36.32/36.52      inference('demod', [status(thm)], ['483', '484'])).
% 36.32/36.52  thf('486', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('487', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('488', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('489', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('490', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('491', plain, (![X10 : $i]: ((k2_zfmisc_1 @ sk_C_2 @ X10) = (sk_C_2))),
% 36.32/36.52      inference('demod', [status(thm)], ['468', '469', '470'])).
% 36.32/36.52  thf('492', plain, ((v1_funct_1 @ sk_C_2)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('493', plain,
% 36.32/36.52      (![X0 : $i]:
% 36.32/36.52         ((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 36.32/36.52          | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ X0)
% 36.32/36.52          | ~ (l1_pre_topc @ X0)
% 36.32/36.52          | ~ (v2_pre_topc @ X0))),
% 36.32/36.52      inference('demod', [status(thm)],
% 36.32/36.52                ['466', '467', '471', '472', '473', '474', '475', '476', 
% 36.32/36.52                 '477', '478', '479', '480', '481', '482', '485', '486', 
% 36.32/36.52                 '487', '488', '489', '490', '491', '492'])).
% 36.32/36.52  thf('494', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52        | (v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['461', '493'])).
% 36.32/36.52  thf('495', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('496', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('497', plain,
% 36.32/36.52      ((v5_pre_topc @ sk_C_2 @ sk_A @ 
% 36.32/36.52        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 36.32/36.52      inference('demod', [status(thm)], ['494', '495', '496'])).
% 36.32/36.52  thf('498', plain,
% 36.32/36.52      (((v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52         (g1_pre_topc @ sk_C_2 @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (v2_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('demod', [status(thm)], ['460', '497'])).
% 36.32/36.52  thf('499', plain,
% 36.32/36.52      (~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 36.32/36.52      inference('simpl_trail', [status(thm)], ['373', '377'])).
% 36.32/36.52  thf('500', plain, (((sk_C_2) = (u1_struct_0 @ sk_A))),
% 36.32/36.52      inference('clc', [status(thm)], ['450', '453'])).
% 36.32/36.52  thf('501', plain,
% 36.32/36.52      (~ (v5_pre_topc @ sk_C_2 @ 
% 36.32/36.52          (g1_pre_topc @ sk_C_2 @ (u1_pre_topc @ sk_A)) @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 36.32/36.52      inference('demod', [status(thm)], ['499', '500'])).
% 36.32/36.52  thf('502', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ 
% 36.32/36.52           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('clc', [status(thm)], ['498', '501'])).
% 36.32/36.52  thf('503', plain,
% 36.32/36.52      ((~ (v2_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (l1_pre_topc @ sk_B_1)
% 36.32/36.52        | ~ (l1_pre_topc @ 
% 36.32/36.52             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 36.32/36.52      inference('sup-', [status(thm)], ['3', '502'])).
% 36.32/36.52  thf('504', plain, ((v2_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('505', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('506', plain,
% 36.32/36.52      (~ (l1_pre_topc @ 
% 36.32/36.52          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 36.32/36.52      inference('demod', [status(thm)], ['503', '504', '505'])).
% 36.32/36.52  thf('507', plain, (~ (l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('sup-', [status(thm)], ['2', '506'])).
% 36.32/36.52  thf('508', plain, ((l1_pre_topc @ sk_B_1)),
% 36.32/36.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.32/36.52  thf('509', plain, ($false), inference('demod', [status(thm)], ['507', '508'])).
% 36.32/36.52  
% 36.32/36.52  % SZS output end Refutation
% 36.32/36.52  
% 36.32/36.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
