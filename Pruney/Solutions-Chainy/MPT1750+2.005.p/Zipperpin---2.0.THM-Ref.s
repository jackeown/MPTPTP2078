%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OjH4KFaAVW

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:39 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  208 (2633 expanded)
%              Number of leaves         :   42 ( 776 expanded)
%              Depth                    :   32
%              Number of atoms          : 2121 (67219 expanded)
%              Number of equality atoms :   48 (1087 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t60_tmap_1,conjecture,(
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
                 => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                   => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( m1_pre_topc @ X41 @ X43 )
      | ( r1_tarski @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X24: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X22 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( X37
       != ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( m1_pre_topc @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('22',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) @ X39 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','34','35','36','37'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ( m1_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( l1_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('48',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( m1_pre_topc @ X41 @ X43 )
      | ( r1_tarski @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','56'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X27 @ X31 )
      | ( X27 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('60',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('67',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('69',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('73',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','56'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

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

thf('77',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( ( k2_tmap_1 @ X35 @ X33 @ X36 @ X34 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) @ X36 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X43 ) )
      | ( m1_pre_topc @ X41 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','56'])).

thf('106',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( ( k2_tmap_1 @ X35 @ X33 @ X36 @ X34 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) @ X36 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('109',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('110',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','113','114','115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf('127',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X14 ) ) )
      | ( r2_relset_1 @ X11 @ X14 @ ( k2_partfun1 @ X11 @ X14 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_2])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_B ) ) @ sk_D ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('134',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('135',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('136',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_D ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('138',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('141',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['139','147'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('149',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( X3 = X6 )
      | ~ ( r2_relset_1 @ X4 @ X5 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['138','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','56'])).

thf('153',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( sk_D
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','153'])).

thf('155',plain,
    ( sk_D
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['94','154'])).

thf('156',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['73','155'])).

thf('157',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','156'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('158',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('161',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['0','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OjH4KFaAVW
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.61/3.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.61/3.82  % Solved by: fo/fo7.sh
% 3.61/3.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.61/3.82  % done 2224 iterations in 3.360s
% 3.61/3.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.61/3.82  % SZS output start Refutation
% 3.61/3.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.61/3.82  thf(sk_B_type, type, sk_B: $i).
% 3.61/3.82  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.61/3.82  thf(sk_D_type, type, sk_D: $i).
% 3.61/3.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.61/3.82  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 3.61/3.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.61/3.82  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.61/3.82  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.61/3.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.61/3.82  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.61/3.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.61/3.82  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 3.61/3.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.61/3.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.61/3.82  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 3.61/3.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.61/3.82  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.61/3.82  thf(sk_A_type, type, sk_A: $i).
% 3.61/3.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.61/3.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.61/3.82  thf(sk_C_type, type, sk_C: $i).
% 3.61/3.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.61/3.82  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.61/3.82  thf(t60_tmap_1, conjecture,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.82       ( ![B:$i]:
% 3.61/3.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.61/3.82             ( l1_pre_topc @ B ) ) =>
% 3.61/3.82           ( ![C:$i]:
% 3.61/3.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 3.61/3.82               ( ![D:$i]:
% 3.61/3.82                 ( ( ( v1_funct_1 @ D ) & 
% 3.61/3.82                     ( v1_funct_2 @
% 3.61/3.82                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 3.61/3.82                     ( m1_subset_1 @
% 3.61/3.82                       D @ 
% 3.61/3.82                       ( k1_zfmisc_1 @
% 3.61/3.82                         ( k2_zfmisc_1 @
% 3.61/3.82                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 3.61/3.82                   ( ( ( g1_pre_topc @
% 3.61/3.82                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 3.61/3.82                       ( g1_pre_topc @
% 3.61/3.82                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 3.61/3.82                     ( r1_funct_2 @
% 3.61/3.82                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.61/3.82                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 3.61/3.82                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 3.61/3.82  thf(zf_stmt_0, negated_conjecture,
% 3.61/3.82    (~( ![A:$i]:
% 3.61/3.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.61/3.82            ( l1_pre_topc @ A ) ) =>
% 3.61/3.82          ( ![B:$i]:
% 3.61/3.82            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.61/3.82                ( l1_pre_topc @ B ) ) =>
% 3.61/3.82              ( ![C:$i]:
% 3.61/3.82                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 3.61/3.82                  ( ![D:$i]:
% 3.61/3.82                    ( ( ( v1_funct_1 @ D ) & 
% 3.61/3.82                        ( v1_funct_2 @
% 3.61/3.82                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 3.61/3.82                        ( m1_subset_1 @
% 3.61/3.82                          D @ 
% 3.61/3.82                          ( k1_zfmisc_1 @
% 3.61/3.82                            ( k2_zfmisc_1 @
% 3.61/3.82                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 3.61/3.82                      ( ( ( g1_pre_topc @
% 3.61/3.82                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 3.61/3.82                          ( g1_pre_topc @
% 3.61/3.82                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 3.61/3.82                        ( r1_funct_2 @
% 3.61/3.82                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.61/3.82                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 3.61/3.82                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 3.61/3.82    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 3.61/3.82  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('1', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(t2_tsep_1, axiom,
% 3.61/3.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 3.61/3.82  thf('2', plain,
% 3.61/3.82      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 3.61/3.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.61/3.82  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(t4_tsep_1, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.82       ( ![B:$i]:
% 3.61/3.82         ( ( m1_pre_topc @ B @ A ) =>
% 3.61/3.82           ( ![C:$i]:
% 3.61/3.82             ( ( m1_pre_topc @ C @ A ) =>
% 3.61/3.82               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 3.61/3.82                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 3.61/3.82  thf('4', plain,
% 3.61/3.82      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X41 @ X42)
% 3.61/3.82          | ~ (m1_pre_topc @ X41 @ X43)
% 3.61/3.82          | (r1_tarski @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X43))
% 3.61/3.82          | ~ (m1_pre_topc @ X43 @ X42)
% 3.61/3.82          | ~ (l1_pre_topc @ X42)
% 3.61/3.82          | ~ (v2_pre_topc @ X42))),
% 3.61/3.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 3.61/3.82  thf('5', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (~ (v2_pre_topc @ sk_B)
% 3.61/3.82          | ~ (l1_pre_topc @ sk_B)
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ sk_B)
% 3.61/3.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 3.61/3.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 3.61/3.82      inference('sup-', [status(thm)], ['3', '4'])).
% 3.61/3.82  thf('6', plain, ((v2_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('8', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X0 @ sk_B)
% 3.61/3.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 3.61/3.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 3.61/3.82      inference('demod', [status(thm)], ['5', '6', '7'])).
% 3.61/3.82  thf('9', plain,
% 3.61/3.82      ((~ (l1_pre_topc @ sk_B)
% 3.61/3.82        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 3.61/3.82        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.61/3.82      inference('sup-', [status(thm)], ['2', '8'])).
% 3.61/3.82  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('12', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.61/3.82      inference('demod', [status(thm)], ['9', '10', '11'])).
% 3.61/3.82  thf(d10_xboole_0, axiom,
% 3.61/3.82    (![A:$i,B:$i]:
% 3.61/3.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.61/3.82  thf('13', plain,
% 3.61/3.82      (![X0 : $i, X2 : $i]:
% 3.61/3.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.61/3.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.61/3.82  thf('14', plain,
% 3.61/3.82      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 3.61/3.82        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('sup-', [status(thm)], ['12', '13'])).
% 3.61/3.82  thf('15', plain,
% 3.61/3.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 3.61/3.82         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('16', plain,
% 3.61/3.82      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 3.61/3.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.61/3.82  thf(fc6_pre_topc, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.82       ( ( v1_pre_topc @
% 3.61/3.82           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 3.61/3.82         ( v2_pre_topc @
% 3.61/3.82           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 3.61/3.82  thf('17', plain,
% 3.61/3.82      (![X24 : $i]:
% 3.61/3.82         ((v2_pre_topc @ 
% 3.61/3.82           (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 3.61/3.82          | ~ (l1_pre_topc @ X24)
% 3.61/3.82          | ~ (v2_pre_topc @ X24))),
% 3.61/3.82      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 3.61/3.82  thf(dt_u1_pre_topc, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( l1_pre_topc @ A ) =>
% 3.61/3.82       ( m1_subset_1 @
% 3.61/3.82         ( u1_pre_topc @ A ) @ 
% 3.61/3.82         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 3.61/3.82  thf('18', plain,
% 3.61/3.82      (![X22 : $i]:
% 3.61/3.82         ((m1_subset_1 @ (u1_pre_topc @ X22) @ 
% 3.61/3.82           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 3.61/3.82          | ~ (l1_pre_topc @ X22))),
% 3.61/3.82      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 3.61/3.82  thf(dt_g1_pre_topc, axiom,
% 3.61/3.82    (![A:$i,B:$i]:
% 3.61/3.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.61/3.82       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 3.61/3.82         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 3.61/3.82  thf('19', plain,
% 3.61/3.82      (![X17 : $i, X18 : $i]:
% 3.61/3.82         ((l1_pre_topc @ (g1_pre_topc @ X17 @ X18))
% 3.61/3.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 3.61/3.82      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 3.61/3.82  thf('20', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X0)
% 3.61/3.82          | (l1_pre_topc @ 
% 3.61/3.82             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.61/3.82      inference('sup-', [status(thm)], ['18', '19'])).
% 3.61/3.82  thf(t12_tmap_1, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( l1_pre_topc @ A ) =>
% 3.61/3.82       ( ![B:$i]:
% 3.61/3.82         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.61/3.82           ( ![C:$i]:
% 3.61/3.82             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 3.61/3.82               ( ( ( B ) =
% 3.61/3.82                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 3.61/3.82                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 3.61/3.82  thf('21', plain,
% 3.61/3.82      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.61/3.82         (~ (v2_pre_topc @ X37)
% 3.61/3.82          | ~ (l1_pre_topc @ X37)
% 3.61/3.82          | ((X37) != (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 3.61/3.82          | ~ (m1_pre_topc @ X37 @ X39)
% 3.61/3.82          | (m1_pre_topc @ X38 @ X39)
% 3.61/3.82          | ~ (l1_pre_topc @ X38)
% 3.61/3.82          | ~ (v2_pre_topc @ X38)
% 3.61/3.82          | ~ (l1_pre_topc @ X39))),
% 3.61/3.82      inference('cnf', [status(esa)], [t12_tmap_1])).
% 3.61/3.82  thf('22', plain,
% 3.61/3.82      (![X38 : $i, X39 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X39)
% 3.61/3.82          | ~ (v2_pre_topc @ X38)
% 3.61/3.82          | ~ (l1_pre_topc @ X38)
% 3.61/3.82          | (m1_pre_topc @ X38 @ X39)
% 3.61/3.82          | ~ (m1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)) @ X39)
% 3.61/3.82          | ~ (l1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 3.61/3.82          | ~ (v2_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))))),
% 3.61/3.82      inference('simplify', [status(thm)], ['21'])).
% 3.61/3.82  thf('23', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.61/3.82          | ~ (m1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 3.61/3.82          | (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X1))),
% 3.61/3.82      inference('sup-', [status(thm)], ['20', '22'])).
% 3.61/3.82  thf('24', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X1)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | ~ (m1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 3.61/3.82          | ~ (v2_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.61/3.82          | ~ (l1_pre_topc @ X0))),
% 3.61/3.82      inference('simplify', [status(thm)], ['23'])).
% 3.61/3.82  thf('25', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (m1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 3.61/3.82          | (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X1))),
% 3.61/3.82      inference('sup-', [status(thm)], ['17', '24'])).
% 3.61/3.82  thf('26', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X1)
% 3.61/3.82          | (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | ~ (m1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0))),
% 3.61/3.82      inference('simplify', [status(thm)], ['25'])).
% 3.61/3.82  thf('27', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ 
% 3.61/3.82             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | (m1_pre_topc @ X0 @ 
% 3.61/3.82             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.61/3.82          | ~ (l1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.61/3.82      inference('sup-', [status(thm)], ['16', '26'])).
% 3.61/3.82  thf('28', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((m1_pre_topc @ X0 @ 
% 3.61/3.82           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ 
% 3.61/3.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.61/3.82      inference('simplify', [status(thm)], ['27'])).
% 3.61/3.82  thf('29', plain,
% 3.61/3.82      ((~ (l1_pre_topc @ 
% 3.61/3.82           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 3.61/3.82        | ~ (v2_pre_topc @ sk_B)
% 3.61/3.82        | ~ (l1_pre_topc @ sk_B)
% 3.61/3.82        | (m1_pre_topc @ sk_B @ 
% 3.61/3.82           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 3.61/3.82      inference('sup-', [status(thm)], ['15', '28'])).
% 3.61/3.82  thf('30', plain,
% 3.61/3.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 3.61/3.82         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('31', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X0)
% 3.61/3.82          | (l1_pre_topc @ 
% 3.61/3.82             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.61/3.82      inference('sup-', [status(thm)], ['18', '19'])).
% 3.61/3.82  thf('32', plain,
% 3.61/3.82      (((l1_pre_topc @ 
% 3.61/3.82         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 3.61/3.82        | ~ (l1_pre_topc @ sk_B))),
% 3.61/3.82      inference('sup+', [status(thm)], ['30', '31'])).
% 3.61/3.82  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('34', plain,
% 3.61/3.82      ((l1_pre_topc @ 
% 3.61/3.82        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 3.61/3.82      inference('demod', [status(thm)], ['32', '33'])).
% 3.61/3.82  thf('35', plain, ((v2_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('37', plain,
% 3.61/3.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 3.61/3.82         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('38', plain,
% 3.61/3.82      ((m1_pre_topc @ sk_B @ 
% 3.61/3.82        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 3.61/3.82      inference('demod', [status(thm)], ['29', '34', '35', '36', '37'])).
% 3.61/3.82  thf(t59_pre_topc, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( l1_pre_topc @ A ) =>
% 3.61/3.82       ( ![B:$i]:
% 3.61/3.82         ( ( m1_pre_topc @
% 3.61/3.82             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 3.61/3.82           ( m1_pre_topc @ B @ A ) ) ) ))).
% 3.61/3.82  thf('39', plain,
% 3.61/3.82      (![X25 : $i, X26 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X25 @ 
% 3.61/3.82             (g1_pre_topc @ (u1_struct_0 @ X26) @ (u1_pre_topc @ X26)))
% 3.61/3.82          | (m1_pre_topc @ X25 @ X26)
% 3.61/3.82          | ~ (l1_pre_topc @ X26))),
% 3.61/3.82      inference('cnf', [status(esa)], [t59_pre_topc])).
% 3.61/3.82  thf('40', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 3.61/3.82      inference('sup-', [status(thm)], ['38', '39'])).
% 3.61/3.82  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(dt_m1_pre_topc, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( l1_pre_topc @ A ) =>
% 3.61/3.82       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.61/3.82  thf('42', plain,
% 3.61/3.82      (![X20 : $i, X21 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X20 @ X21)
% 3.61/3.82          | (l1_pre_topc @ X20)
% 3.61/3.82          | ~ (l1_pre_topc @ X21))),
% 3.61/3.82      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.61/3.82  thf('43', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 3.61/3.82      inference('sup-', [status(thm)], ['41', '42'])).
% 3.61/3.82  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 3.61/3.82      inference('demod', [status(thm)], ['43', '44'])).
% 3.61/3.82  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 3.61/3.82      inference('demod', [status(thm)], ['40', '45'])).
% 3.61/3.82  thf('47', plain,
% 3.61/3.82      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 3.61/3.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.61/3.82  thf('48', plain,
% 3.61/3.82      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X41 @ X42)
% 3.61/3.82          | ~ (m1_pre_topc @ X41 @ X43)
% 3.61/3.82          | (r1_tarski @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X43))
% 3.61/3.82          | ~ (m1_pre_topc @ X43 @ X42)
% 3.61/3.82          | ~ (l1_pre_topc @ X42)
% 3.61/3.82          | ~ (v2_pre_topc @ X42))),
% 3.61/3.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 3.61/3.82  thf('49', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (m1_pre_topc @ X1 @ X0)
% 3.61/3.82          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.61/3.82      inference('sup-', [status(thm)], ['47', '48'])).
% 3.61/3.82  thf('50', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 3.61/3.82          | ~ (m1_pre_topc @ X1 @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | ~ (l1_pre_topc @ X0))),
% 3.61/3.82      inference('simplify', [status(thm)], ['49'])).
% 3.61/3.82  thf('51', plain,
% 3.61/3.82      ((~ (l1_pre_topc @ sk_B)
% 3.61/3.82        | ~ (v2_pre_topc @ sk_B)
% 3.61/3.82        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 3.61/3.82        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('sup-', [status(thm)], ['46', '50'])).
% 3.61/3.82  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('53', plain, ((v2_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('55', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 3.61/3.82  thf('56', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('57', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['1', '56'])).
% 3.61/3.82  thf('58', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['1', '56'])).
% 3.61/3.82  thf(redefinition_r1_funct_2, axiom,
% 3.61/3.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.61/3.82     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 3.61/3.82         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 3.61/3.82         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.61/3.82         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 3.61/3.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.61/3.82       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 3.61/3.82  thf('59', plain,
% 3.61/3.82      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.61/3.82          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 3.61/3.82          | ~ (v1_funct_1 @ X27)
% 3.61/3.82          | (v1_xboole_0 @ X30)
% 3.61/3.82          | (v1_xboole_0 @ X29)
% 3.61/3.82          | ~ (v1_funct_1 @ X31)
% 3.61/3.82          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 3.61/3.82          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 3.61/3.82          | (r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X27 @ X31)
% 3.61/3.82          | ((X27) != (X31)))),
% 3.61/3.82      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 3.61/3.82  thf('60', plain,
% 3.61/3.82      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.61/3.82         ((r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X31 @ X31)
% 3.61/3.82          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 3.61/3.82          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 3.61/3.82          | (v1_xboole_0 @ X29)
% 3.61/3.82          | (v1_xboole_0 @ X30)
% 3.61/3.82          | ~ (v1_funct_1 @ X31)
% 3.61/3.82          | ~ (v1_funct_2 @ X31 @ X28 @ X29)
% 3.61/3.82          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.61/3.82      inference('simplify', [status(thm)], ['59'])).
% 3.61/3.82  thf('61', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.61/3.82          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 3.61/3.82          | ~ (v1_funct_1 @ sk_D)
% 3.61/3.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.61/3.82          | (v1_xboole_0 @ X0)
% 3.61/3.82          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 3.61/3.82          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 3.61/3.82             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 3.61/3.82      inference('sup-', [status(thm)], ['58', '60'])).
% 3.61/3.82  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('63', plain,
% 3.61/3.82      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('64', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('65', plain,
% 3.61/3.82      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('demod', [status(thm)], ['63', '64'])).
% 3.61/3.82  thf('66', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.61/3.82          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 3.61/3.82          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.61/3.82          | (v1_xboole_0 @ X0)
% 3.61/3.82          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 3.61/3.82             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 3.61/3.82      inference('demod', [status(thm)], ['61', '62', '65'])).
% 3.61/3.82  thf('67', plain,
% 3.61/3.82      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 3.61/3.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.61/3.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.61/3.82        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 3.61/3.82      inference('sup-', [status(thm)], ['57', '66'])).
% 3.61/3.82  thf('68', plain,
% 3.61/3.82      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('demod', [status(thm)], ['63', '64'])).
% 3.61/3.82  thf('69', plain,
% 3.61/3.82      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 3.61/3.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.61/3.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.82      inference('demod', [status(thm)], ['67', '68'])).
% 3.61/3.82  thf('70', plain,
% 3.61/3.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.61/3.82        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 3.61/3.82      inference('simplify', [status(thm)], ['69'])).
% 3.61/3.82  thf('71', plain,
% 3.61/3.82      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('72', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('73', plain,
% 3.61/3.82      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['71', '72'])).
% 3.61/3.82  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('75', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['1', '56'])).
% 3.61/3.82  thf('76', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf(d4_tmap_1, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.82       ( ![B:$i]:
% 3.61/3.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.61/3.82             ( l1_pre_topc @ B ) ) =>
% 3.61/3.82           ( ![C:$i]:
% 3.61/3.82             ( ( ( v1_funct_1 @ C ) & 
% 3.61/3.82                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.61/3.82                 ( m1_subset_1 @
% 3.61/3.82                   C @ 
% 3.61/3.82                   ( k1_zfmisc_1 @
% 3.61/3.82                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.61/3.82               ( ![D:$i]:
% 3.61/3.82                 ( ( m1_pre_topc @ D @ A ) =>
% 3.61/3.82                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 3.61/3.82                     ( k2_partfun1 @
% 3.61/3.82                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 3.61/3.82                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 3.61/3.82  thf('77', plain,
% 3.61/3.82      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.61/3.82         ((v2_struct_0 @ X33)
% 3.61/3.82          | ~ (v2_pre_topc @ X33)
% 3.61/3.82          | ~ (l1_pre_topc @ X33)
% 3.61/3.82          | ~ (m1_pre_topc @ X34 @ X35)
% 3.61/3.82          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 3.61/3.82                 X36 @ (u1_struct_0 @ X34)))
% 3.61/3.82          | ~ (m1_subset_1 @ X36 @ 
% 3.61/3.82               (k1_zfmisc_1 @ 
% 3.61/3.82                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 3.61/3.82          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 3.61/3.82          | ~ (v1_funct_1 @ X36)
% 3.61/3.82          | ~ (l1_pre_topc @ X35)
% 3.61/3.82          | ~ (v2_pre_topc @ X35)
% 3.61/3.82          | (v2_struct_0 @ X35))),
% 3.61/3.82      inference('cnf', [status(esa)], [d4_tmap_1])).
% 3.61/3.82  thf('78', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ X1 @ 
% 3.61/3.82             (k1_zfmisc_1 @ 
% 3.61/3.82              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.61/3.82          | (v2_struct_0 @ sk_B)
% 3.61/3.82          | ~ (v2_pre_topc @ sk_B)
% 3.61/3.82          | ~ (l1_pre_topc @ sk_B)
% 3.61/3.82          | ~ (v1_funct_1 @ X1)
% 3.61/3.82          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 3.61/3.82          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 3.61/3.82                 X1 @ (u1_struct_0 @ X2)))
% 3.61/3.82          | ~ (m1_pre_topc @ X2 @ sk_B)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | (v2_struct_0 @ X0))),
% 3.61/3.82      inference('sup-', [status(thm)], ['76', '77'])).
% 3.61/3.82  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('81', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('82', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('83', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ X1 @ 
% 3.61/3.82             (k1_zfmisc_1 @ 
% 3.61/3.82              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.61/3.82          | (v2_struct_0 @ sk_B)
% 3.61/3.82          | ~ (v1_funct_1 @ X1)
% 3.61/3.82          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 3.61/3.82          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 3.61/3.82                 X1 @ (u1_struct_0 @ X2)))
% 3.61/3.82          | ~ (m1_pre_topc @ X2 @ sk_B)
% 3.61/3.82          | ~ (l1_pre_topc @ X0)
% 3.61/3.82          | ~ (v2_pre_topc @ X0)
% 3.61/3.82          | (v2_struct_0 @ X0))),
% 3.61/3.82      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 3.61/3.82  thf('84', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((v2_struct_0 @ sk_A)
% 3.61/3.82          | ~ (v2_pre_topc @ sk_A)
% 3.61/3.82          | ~ (l1_pre_topc @ sk_A)
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ sk_B)
% 3.61/3.82          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82                 sk_D @ (u1_struct_0 @ X0)))
% 3.61/3.82          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 3.61/3.82          | ~ (v1_funct_1 @ sk_D)
% 3.61/3.82          | (v2_struct_0 @ sk_B))),
% 3.61/3.82      inference('sup-', [status(thm)], ['75', '83'])).
% 3.61/3.82  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('87', plain,
% 3.61/3.82      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('demod', [status(thm)], ['63', '64'])).
% 3.61/3.82  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('89', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((v2_struct_0 @ sk_A)
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ sk_B)
% 3.61/3.82          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82                 sk_D @ (u1_struct_0 @ X0)))
% 3.61/3.82          | (v2_struct_0 @ sk_B))),
% 3.61/3.82      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 3.61/3.82  thf('90', plain,
% 3.61/3.82      (((v2_struct_0 @ sk_B)
% 3.61/3.82        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 3.61/3.82            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82               sk_D @ (u1_struct_0 @ sk_C)))
% 3.61/3.82        | (v2_struct_0 @ sk_A))),
% 3.61/3.82      inference('sup-', [status(thm)], ['74', '89'])).
% 3.61/3.82  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('92', plain,
% 3.61/3.82      (((v2_struct_0 @ sk_A)
% 3.61/3.82        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 3.61/3.82            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82               sk_D @ (u1_struct_0 @ sk_C))))),
% 3.61/3.82      inference('clc', [status(thm)], ['90', '91'])).
% 3.61/3.82  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('94', plain,
% 3.61/3.82      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 3.61/3.82         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('clc', [status(thm)], ['92', '93'])).
% 3.61/3.82  thf('95', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('96', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.61/3.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.61/3.82  thf('97', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.61/3.82      inference('simplify', [status(thm)], ['96'])).
% 3.61/3.82  thf('98', plain,
% 3.61/3.82      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X41 @ X42)
% 3.61/3.82          | ~ (r1_tarski @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X43))
% 3.61/3.82          | (m1_pre_topc @ X41 @ X43)
% 3.61/3.82          | ~ (m1_pre_topc @ X43 @ X42)
% 3.61/3.82          | ~ (l1_pre_topc @ X42)
% 3.61/3.82          | ~ (v2_pre_topc @ X42))),
% 3.61/3.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 3.61/3.82  thf('99', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         (~ (v2_pre_topc @ X1)
% 3.61/3.82          | ~ (l1_pre_topc @ X1)
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | (m1_pre_topc @ X0 @ X0)
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.61/3.82      inference('sup-', [status(thm)], ['97', '98'])).
% 3.61/3.82  thf('100', plain,
% 3.61/3.82      (![X0 : $i, X1 : $i]:
% 3.61/3.82         ((m1_pre_topc @ X0 @ X0)
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ X1)
% 3.61/3.82          | ~ (l1_pre_topc @ X1)
% 3.61/3.82          | ~ (v2_pre_topc @ X1))),
% 3.61/3.82      inference('simplify', [status(thm)], ['99'])).
% 3.61/3.82  thf('101', plain,
% 3.61/3.82      ((~ (v2_pre_topc @ sk_B)
% 3.61/3.82        | ~ (l1_pre_topc @ sk_B)
% 3.61/3.82        | (m1_pre_topc @ sk_C @ sk_C))),
% 3.61/3.82      inference('sup-', [status(thm)], ['95', '100'])).
% 3.61/3.82  thf('102', plain, ((v2_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.61/3.82      inference('demod', [status(thm)], ['101', '102', '103'])).
% 3.61/3.82  thf('105', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['1', '56'])).
% 3.61/3.82  thf('106', plain,
% 3.61/3.82      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.61/3.82         ((v2_struct_0 @ X33)
% 3.61/3.82          | ~ (v2_pre_topc @ X33)
% 3.61/3.82          | ~ (l1_pre_topc @ X33)
% 3.61/3.82          | ~ (m1_pre_topc @ X34 @ X35)
% 3.61/3.82          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 3.61/3.82                 X36 @ (u1_struct_0 @ X34)))
% 3.61/3.82          | ~ (m1_subset_1 @ X36 @ 
% 3.61/3.82               (k1_zfmisc_1 @ 
% 3.61/3.82                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 3.61/3.82          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 3.61/3.82          | ~ (v1_funct_1 @ X36)
% 3.61/3.82          | ~ (l1_pre_topc @ X35)
% 3.61/3.82          | ~ (v2_pre_topc @ X35)
% 3.61/3.82          | (v2_struct_0 @ X35))),
% 3.61/3.82      inference('cnf', [status(esa)], [d4_tmap_1])).
% 3.61/3.82  thf('107', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((v2_struct_0 @ sk_C)
% 3.61/3.82          | ~ (v2_pre_topc @ sk_C)
% 3.61/3.82          | ~ (l1_pre_topc @ sk_C)
% 3.61/3.82          | ~ (v1_funct_1 @ sk_D)
% 3.61/3.82          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 3.61/3.82          | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82                 sk_D @ (u1_struct_0 @ X0)))
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.61/3.82          | ~ (l1_pre_topc @ sk_A)
% 3.61/3.82          | ~ (v2_pre_topc @ sk_A)
% 3.61/3.82          | (v2_struct_0 @ sk_A))),
% 3.61/3.82      inference('sup-', [status(thm)], ['105', '106'])).
% 3.61/3.82  thf('108', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(cc1_pre_topc, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.82       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 3.61/3.82  thf('109', plain,
% 3.61/3.82      (![X15 : $i, X16 : $i]:
% 3.61/3.82         (~ (m1_pre_topc @ X15 @ X16)
% 3.61/3.82          | (v2_pre_topc @ X15)
% 3.61/3.82          | ~ (l1_pre_topc @ X16)
% 3.61/3.82          | ~ (v2_pre_topc @ X16))),
% 3.61/3.82      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 3.61/3.82  thf('110', plain,
% 3.61/3.82      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_C))),
% 3.61/3.82      inference('sup-', [status(thm)], ['108', '109'])).
% 3.61/3.82  thf('111', plain, ((v2_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('113', plain, ((v2_pre_topc @ sk_C)),
% 3.61/3.82      inference('demod', [status(thm)], ['110', '111', '112'])).
% 3.61/3.82  thf('114', plain, ((l1_pre_topc @ sk_C)),
% 3.61/3.82      inference('demod', [status(thm)], ['43', '44'])).
% 3.61/3.82  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('116', plain,
% 3.61/3.82      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('demod', [status(thm)], ['63', '64'])).
% 3.61/3.82  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('119', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((v2_struct_0 @ sk_C)
% 3.61/3.82          | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0)
% 3.61/3.82              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82                 sk_D @ (u1_struct_0 @ X0)))
% 3.61/3.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.61/3.82          | (v2_struct_0 @ sk_A))),
% 3.61/3.82      inference('demod', [status(thm)],
% 3.61/3.82                ['107', '113', '114', '115', '116', '117', '118'])).
% 3.61/3.82  thf('120', plain,
% 3.61/3.82      (((v2_struct_0 @ sk_A)
% 3.61/3.82        | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 3.61/3.82            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82               sk_D @ (u1_struct_0 @ sk_C)))
% 3.61/3.82        | (v2_struct_0 @ sk_C))),
% 3.61/3.82      inference('sup-', [status(thm)], ['104', '119'])).
% 3.61/3.82  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('122', plain,
% 3.61/3.82      (((v2_struct_0 @ sk_C)
% 3.61/3.82        | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 3.61/3.82            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82               sk_D @ (u1_struct_0 @ sk_C))))),
% 3.61/3.82      inference('clc', [status(thm)], ['120', '121'])).
% 3.61/3.82  thf('123', plain, (~ (v2_struct_0 @ sk_C)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('124', plain,
% 3.61/3.82      (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 3.61/3.82         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('clc', [status(thm)], ['122', '123'])).
% 3.61/3.82  thf('125', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.61/3.82      inference('simplify', [status(thm)], ['96'])).
% 3.61/3.82  thf('126', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(t40_funct_2, axiom,
% 3.61/3.82    (![A:$i,B:$i,C:$i,D:$i]:
% 3.61/3.82     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.61/3.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.61/3.82       ( ( r1_tarski @ A @ C ) =>
% 3.61/3.82         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 3.61/3.82  thf('127', plain,
% 3.61/3.82      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.61/3.82         (~ (r1_tarski @ X11 @ X12)
% 3.61/3.82          | ~ (v1_funct_1 @ X13)
% 3.61/3.82          | ~ (v1_funct_2 @ X13 @ X11 @ X14)
% 3.61/3.82          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X14)))
% 3.61/3.82          | (r2_relset_1 @ X11 @ X14 @ (k2_partfun1 @ X11 @ X14 @ X13 @ X12) @ 
% 3.61/3.82             X13))),
% 3.61/3.82      inference('cnf', [status(esa)], [t40_funct_2])).
% 3.61/3.82  thf('128', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            X0) @ 
% 3.61/3.82           sk_D)
% 3.61/3.82          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.61/3.82          | ~ (v1_funct_1 @ sk_D)
% 3.61/3.82          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 3.61/3.82      inference('sup-', [status(thm)], ['126', '127'])).
% 3.61/3.82  thf('129', plain,
% 3.61/3.82      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('131', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            X0) @ 
% 3.61/3.82           sk_D)
% 3.61/3.82          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 3.61/3.82      inference('demod', [status(thm)], ['128', '129', '130'])).
% 3.61/3.82  thf('132', plain,
% 3.61/3.82      ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82        (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82         (u1_struct_0 @ sk_B)) @ 
% 3.61/3.82        sk_D)),
% 3.61/3.82      inference('sup-', [status(thm)], ['125', '131'])).
% 3.61/3.82  thf('133', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('134', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('135', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('136', plain,
% 3.61/3.82      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82        (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82         (u1_struct_0 @ sk_C)) @ 
% 3.61/3.82        sk_D)),
% 3.61/3.82      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 3.61/3.82  thf('137', plain,
% 3.61/3.82      (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 3.61/3.82         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('clc', [status(thm)], ['122', '123'])).
% 3.61/3.82  thf('138', plain,
% 3.61/3.82      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82        (k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) @ sk_D)),
% 3.61/3.82      inference('demod', [status(thm)], ['136', '137'])).
% 3.61/3.82  thf('139', plain,
% 3.61/3.82      (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 3.61/3.82         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('clc', [status(thm)], ['122', '123'])).
% 3.61/3.82  thf('140', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(dt_k2_partfun1, axiom,
% 3.61/3.82    (![A:$i,B:$i,C:$i,D:$i]:
% 3.61/3.82     ( ( ( v1_funct_1 @ C ) & 
% 3.61/3.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.61/3.82       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 3.61/3.82         ( m1_subset_1 @
% 3.61/3.82           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 3.61/3.82           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.61/3.82  thf('141', plain,
% 3.61/3.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 3.61/3.82          | ~ (v1_funct_1 @ X7)
% 3.61/3.82          | (m1_subset_1 @ (k2_partfun1 @ X8 @ X9 @ X7 @ X10) @ 
% 3.61/3.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.61/3.82      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.61/3.82  thf('142', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         ((m1_subset_1 @ 
% 3.61/3.82           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            X0) @ 
% 3.61/3.82           (k1_zfmisc_1 @ 
% 3.61/3.82            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 3.61/3.82          | ~ (v1_funct_1 @ sk_D))),
% 3.61/3.82      inference('sup-', [status(thm)], ['140', '141'])).
% 3.61/3.82  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf('144', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (m1_subset_1 @ 
% 3.61/3.82          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82           X0) @ 
% 3.61/3.82          (k1_zfmisc_1 @ 
% 3.61/3.82           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['142', '143'])).
% 3.61/3.82  thf('145', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('146', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 3.61/3.82      inference('demod', [status(thm)], ['14', '55'])).
% 3.61/3.82  thf('147', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (m1_subset_1 @ 
% 3.61/3.82          (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82           X0) @ 
% 3.61/3.82          (k1_zfmisc_1 @ 
% 3.61/3.82           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['144', '145', '146'])).
% 3.61/3.82  thf('148', plain,
% 3.61/3.82      ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('sup+', [status(thm)], ['139', '147'])).
% 3.61/3.82  thf(redefinition_r2_relset_1, axiom,
% 3.61/3.82    (![A:$i,B:$i,C:$i,D:$i]:
% 3.61/3.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.61/3.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.61/3.82       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.61/3.82  thf('149', plain,
% 3.61/3.82      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.61/3.82         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 3.61/3.82          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 3.61/3.82          | ((X3) = (X6))
% 3.61/3.82          | ~ (r2_relset_1 @ X4 @ X5 @ X3 @ X6))),
% 3.61/3.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.61/3.82  thf('150', plain,
% 3.61/3.82      (![X0 : $i]:
% 3.61/3.82         (~ (r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82             (k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) @ X0)
% 3.61/3.82          | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) = (X0))
% 3.61/3.82          | ~ (m1_subset_1 @ X0 @ 
% 3.61/3.82               (k1_zfmisc_1 @ 
% 3.61/3.82                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 3.61/3.82      inference('sup-', [status(thm)], ['148', '149'])).
% 3.61/3.82  thf('151', plain,
% 3.61/3.82      ((~ (m1_subset_1 @ sk_D @ 
% 3.61/3.82           (k1_zfmisc_1 @ 
% 3.61/3.82            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 3.61/3.82        | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 3.61/3.82      inference('sup-', [status(thm)], ['138', '150'])).
% 3.61/3.82  thf('152', plain,
% 3.61/3.82      ((m1_subset_1 @ sk_D @ 
% 3.61/3.82        (k1_zfmisc_1 @ 
% 3.61/3.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 3.61/3.82      inference('demod', [status(thm)], ['1', '56'])).
% 3.61/3.82  thf('153', plain, (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 3.61/3.82      inference('demod', [status(thm)], ['151', '152'])).
% 3.61/3.82  thf('154', plain,
% 3.61/3.82      (((sk_D)
% 3.61/3.82         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 3.61/3.82            (u1_struct_0 @ sk_C)))),
% 3.61/3.82      inference('demod', [status(thm)], ['124', '153'])).
% 3.61/3.82  thf('155', plain, (((sk_D) = (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 3.61/3.82      inference('sup+', [status(thm)], ['94', '154'])).
% 3.61/3.82  thf('156', plain,
% 3.61/3.82      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 3.61/3.82          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 3.61/3.82      inference('demod', [status(thm)], ['73', '155'])).
% 3.61/3.82  thf('157', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 3.61/3.82      inference('sup-', [status(thm)], ['70', '156'])).
% 3.61/3.82  thf(fc2_struct_0, axiom,
% 3.61/3.82    (![A:$i]:
% 3.61/3.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.61/3.82       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.61/3.82  thf('158', plain,
% 3.61/3.82      (![X23 : $i]:
% 3.61/3.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 3.61/3.82          | ~ (l1_struct_0 @ X23)
% 3.61/3.82          | (v2_struct_0 @ X23))),
% 3.61/3.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.61/3.82  thf('159', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 3.61/3.82      inference('sup-', [status(thm)], ['157', '158'])).
% 3.61/3.82  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.82  thf(dt_l1_pre_topc, axiom,
% 3.61/3.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.61/3.82  thf('161', plain,
% 3.61/3.82      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 3.61/3.82      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.61/3.82  thf('162', plain, ((l1_struct_0 @ sk_A)),
% 3.61/3.82      inference('sup-', [status(thm)], ['160', '161'])).
% 3.61/3.82  thf('163', plain, ((v2_struct_0 @ sk_A)),
% 3.61/3.82      inference('demod', [status(thm)], ['159', '162'])).
% 3.61/3.82  thf('164', plain, ($false), inference('demod', [status(thm)], ['0', '163'])).
% 3.61/3.82  
% 3.61/3.82  % SZS output end Refutation
% 3.61/3.82  
% 3.61/3.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
