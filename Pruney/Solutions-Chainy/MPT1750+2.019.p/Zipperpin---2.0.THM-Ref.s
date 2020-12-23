%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4TosjdDOKf

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:42 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  165 (1166 expanded)
%              Number of leaves         :   46 ( 354 expanded)
%              Depth                    :   29
%              Number of atoms          : 1554 (26013 expanded)
%              Number of equality atoms :   41 ( 429 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('12',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X25: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X23 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( X38
       != ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) )
      | ~ ( m1_pre_topc @ X38 @ X40 )
      | ( m1_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('18',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) @ X40 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','30','31','32','33'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ( m1_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32 )
      | ( X28 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('68',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','49'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

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

thf('72',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( k2_tmap_1 @ X36 @ X34 @ X37 @ X35 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) @ X37 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('78',plain,(
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
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 )
        = ( k7_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81','88','89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('94',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('95',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('99',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','48'])).

thf('103',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['68','108'])).

thf('110',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','109'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('111',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('114',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['0','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4TosjdDOKf
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.78/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/1.01  % Solved by: fo/fo7.sh
% 0.78/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/1.01  % done 609 iterations in 0.544s
% 0.78/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/1.01  % SZS output start Refutation
% 0.78/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.78/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.78/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.78/1.01  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.78/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.78/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/1.01  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.78/1.01  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.78/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.78/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.78/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.78/1.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.78/1.01  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.78/1.01  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.78/1.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.78/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.78/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.78/1.01  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.78/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.78/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.78/1.01  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.78/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.78/1.01  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.78/1.01  thf(t60_tmap_1, conjecture,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.78/1.01       ( ![B:$i]:
% 0.78/1.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.78/1.01             ( l1_pre_topc @ B ) ) =>
% 0.78/1.01           ( ![C:$i]:
% 0.78/1.01             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.78/1.01               ( ![D:$i]:
% 0.78/1.01                 ( ( ( v1_funct_1 @ D ) & 
% 0.78/1.01                     ( v1_funct_2 @
% 0.78/1.01                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.78/1.01                     ( m1_subset_1 @
% 0.78/1.01                       D @ 
% 0.78/1.01                       ( k1_zfmisc_1 @
% 0.78/1.01                         ( k2_zfmisc_1 @
% 0.78/1.01                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.78/1.01                   ( ( ( g1_pre_topc @
% 0.78/1.01                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.78/1.01                       ( g1_pre_topc @
% 0.78/1.01                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.78/1.01                     ( r1_funct_2 @
% 0.78/1.01                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/1.01                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.78/1.01                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.78/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.78/1.01    (~( ![A:$i]:
% 0.78/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.78/1.01            ( l1_pre_topc @ A ) ) =>
% 0.78/1.01          ( ![B:$i]:
% 0.78/1.01            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.78/1.01                ( l1_pre_topc @ B ) ) =>
% 0.78/1.01              ( ![C:$i]:
% 0.78/1.01                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.78/1.01                  ( ![D:$i]:
% 0.78/1.01                    ( ( ( v1_funct_1 @ D ) & 
% 0.78/1.01                        ( v1_funct_2 @
% 0.78/1.01                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.78/1.01                        ( m1_subset_1 @
% 0.78/1.01                          D @ 
% 0.78/1.01                          ( k1_zfmisc_1 @
% 0.78/1.01                            ( k2_zfmisc_1 @
% 0.78/1.01                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.78/1.01                      ( ( ( g1_pre_topc @
% 0.78/1.01                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.78/1.01                          ( g1_pre_topc @
% 0.78/1.01                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.78/1.01                        ( r1_funct_2 @
% 0.78/1.01                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/1.01                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.78/1.01                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.78/1.01    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.78/1.01  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('1', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(t1_tsep_1, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( l1_pre_topc @ A ) =>
% 0.78/1.01       ( ![B:$i]:
% 0.78/1.01         ( ( m1_pre_topc @ B @ A ) =>
% 0.78/1.01           ( m1_subset_1 @
% 0.78/1.01             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.78/1.01  thf('3', plain,
% 0.78/1.01      (![X41 : $i, X42 : $i]:
% 0.78/1.01         (~ (m1_pre_topc @ X41 @ X42)
% 0.78/1.01          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.78/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.78/1.01          | ~ (l1_pre_topc @ X42))),
% 0.78/1.01      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.78/1.01  thf('4', plain,
% 0.78/1.01      ((~ (l1_pre_topc @ sk_B)
% 0.78/1.01        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.78/1.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/1.01  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('6', plain,
% 0.78/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.78/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.78/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.78/1.01  thf(t3_subset, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.78/1.01  thf('7', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i]:
% 0.78/1.01         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.78/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.01  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.78/1.01      inference('sup-', [status(thm)], ['6', '7'])).
% 0.78/1.01  thf(d10_xboole_0, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.78/1.01  thf('9', plain,
% 0.78/1.01      (![X0 : $i, X2 : $i]:
% 0.78/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.78/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.78/1.01  thf('10', plain,
% 0.78/1.01      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.78/1.01        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['8', '9'])).
% 0.78/1.01  thf('11', plain,
% 0.78/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.78/1.01         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(t2_tsep_1, axiom,
% 0.78/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.78/1.01  thf('12', plain,
% 0.78/1.01      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 0.78/1.01      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.78/1.01  thf(fc6_pre_topc, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.78/1.01       ( ( v1_pre_topc @
% 0.78/1.01           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.78/1.01         ( v2_pre_topc @
% 0.78/1.01           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.78/1.01  thf('13', plain,
% 0.78/1.01      (![X25 : $i]:
% 0.78/1.01         ((v2_pre_topc @ 
% 0.78/1.01           (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 0.78/1.01          | ~ (l1_pre_topc @ X25)
% 0.78/1.01          | ~ (v2_pre_topc @ X25))),
% 0.78/1.01      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.78/1.01  thf(dt_u1_pre_topc, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( l1_pre_topc @ A ) =>
% 0.78/1.01       ( m1_subset_1 @
% 0.78/1.01         ( u1_pre_topc @ A ) @ 
% 0.78/1.01         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.78/1.01  thf('14', plain,
% 0.78/1.01      (![X23 : $i]:
% 0.78/1.01         ((m1_subset_1 @ (u1_pre_topc @ X23) @ 
% 0.78/1.01           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.78/1.01          | ~ (l1_pre_topc @ X23))),
% 0.78/1.01      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.78/1.01  thf(dt_g1_pre_topc, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/1.01       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.78/1.01         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.78/1.01  thf('15', plain,
% 0.78/1.01      (![X18 : $i, X19 : $i]:
% 0.78/1.01         ((l1_pre_topc @ (g1_pre_topc @ X18 @ X19))
% 0.78/1.01          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.78/1.01      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.78/1.01  thf('16', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ X0)
% 0.78/1.01          | (l1_pre_topc @ 
% 0.78/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/1.01  thf(t12_tmap_1, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( l1_pre_topc @ A ) =>
% 0.78/1.01       ( ![B:$i]:
% 0.78/1.01         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.78/1.01           ( ![C:$i]:
% 0.78/1.01             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.78/1.01               ( ( ( B ) =
% 0.78/1.01                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.78/1.01                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.78/1.01  thf('17', plain,
% 0.78/1.01      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.78/1.01         (~ (v2_pre_topc @ X38)
% 0.78/1.01          | ~ (l1_pre_topc @ X38)
% 0.78/1.01          | ((X38) != (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39)))
% 0.78/1.01          | ~ (m1_pre_topc @ X38 @ X40)
% 0.78/1.01          | (m1_pre_topc @ X39 @ X40)
% 0.78/1.01          | ~ (l1_pre_topc @ X39)
% 0.78/1.01          | ~ (v2_pre_topc @ X39)
% 0.78/1.01          | ~ (l1_pre_topc @ X40))),
% 0.78/1.01      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.78/1.01  thf('18', plain,
% 0.78/1.01      (![X39 : $i, X40 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ X40)
% 0.78/1.01          | ~ (v2_pre_topc @ X39)
% 0.78/1.01          | ~ (l1_pre_topc @ X39)
% 0.78/1.01          | (m1_pre_topc @ X39 @ X40)
% 0.78/1.01          | ~ (m1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39)) @ X40)
% 0.78/1.01          | ~ (l1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39)))
% 0.78/1.01          | ~ (v2_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39))))),
% 0.78/1.01      inference('simplify', [status(thm)], ['17'])).
% 0.78/1.01  thf('19', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (v2_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.78/1.01          | ~ (m1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.78/1.01          | (m1_pre_topc @ X0 @ X1)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | ~ (l1_pre_topc @ X1))),
% 0.78/1.01      inference('sup-', [status(thm)], ['16', '18'])).
% 0.78/1.01  thf('20', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ X1)
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | (m1_pre_topc @ X0 @ X1)
% 0.78/1.01          | ~ (m1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.78/1.01          | ~ (v2_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.78/1.01          | ~ (l1_pre_topc @ X0))),
% 0.78/1.01      inference('simplify', [status(thm)], ['19'])).
% 0.78/1.01  thf('21', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (v2_pre_topc @ X0)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (m1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.78/1.01          | (m1_pre_topc @ X0 @ X1)
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | ~ (l1_pre_topc @ X1))),
% 0.78/1.01      inference('sup-', [status(thm)], ['13', '20'])).
% 0.78/1.01  thf('22', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ X1)
% 0.78/1.01          | (m1_pre_topc @ X0 @ X1)
% 0.78/1.01          | ~ (m1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (v2_pre_topc @ X0))),
% 0.78/1.01      inference('simplify', [status(thm)], ['21'])).
% 0.78/1.01  thf('23', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ 
% 0.78/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | (m1_pre_topc @ X0 @ 
% 0.78/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.78/1.01          | ~ (l1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['12', '22'])).
% 0.78/1.01  thf('24', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         ((m1_pre_topc @ X0 @ 
% 0.78/1.01           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | ~ (l1_pre_topc @ 
% 0.78/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.78/1.01      inference('simplify', [status(thm)], ['23'])).
% 0.78/1.01  thf('25', plain,
% 0.78/1.01      ((~ (l1_pre_topc @ 
% 0.78/1.01           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.78/1.01        | ~ (v2_pre_topc @ sk_B)
% 0.78/1.01        | ~ (l1_pre_topc @ sk_B)
% 0.78/1.01        | (m1_pre_topc @ sk_B @ 
% 0.78/1.01           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['11', '24'])).
% 0.78/1.01  thf('26', plain,
% 0.78/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.78/1.01         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('27', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         (~ (l1_pre_topc @ X0)
% 0.78/1.01          | (l1_pre_topc @ 
% 0.78/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/1.01  thf('28', plain,
% 0.78/1.01      (((l1_pre_topc @ 
% 0.78/1.01         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.78/1.01        | ~ (l1_pre_topc @ sk_B))),
% 0.78/1.01      inference('sup+', [status(thm)], ['26', '27'])).
% 0.78/1.01  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('30', plain,
% 0.78/1.01      ((l1_pre_topc @ 
% 0.78/1.01        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.78/1.01      inference('demod', [status(thm)], ['28', '29'])).
% 0.78/1.01  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('33', plain,
% 0.78/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.78/1.01         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('34', plain,
% 0.78/1.01      ((m1_pre_topc @ sk_B @ 
% 0.78/1.01        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.78/1.01      inference('demod', [status(thm)], ['25', '30', '31', '32', '33'])).
% 0.78/1.01  thf(t59_pre_topc, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( l1_pre_topc @ A ) =>
% 0.78/1.01       ( ![B:$i]:
% 0.78/1.01         ( ( m1_pre_topc @
% 0.78/1.01             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.78/1.01           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.78/1.01  thf('35', plain,
% 0.78/1.01      (![X26 : $i, X27 : $i]:
% 0.78/1.01         (~ (m1_pre_topc @ X26 @ 
% 0.78/1.01             (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.78/1.01          | (m1_pre_topc @ X26 @ X27)
% 0.78/1.01          | ~ (l1_pre_topc @ X27))),
% 0.78/1.01      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.78/1.01  thf('36', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.78/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.78/1.01  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(dt_m1_pre_topc, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( l1_pre_topc @ A ) =>
% 0.78/1.01       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.78/1.01  thf('38', plain,
% 0.78/1.01      (![X21 : $i, X22 : $i]:
% 0.78/1.01         (~ (m1_pre_topc @ X21 @ X22)
% 0.78/1.01          | (l1_pre_topc @ X21)
% 0.78/1.01          | ~ (l1_pre_topc @ X22))),
% 0.78/1.01      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.78/1.01  thf('39', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.78/1.01      inference('sup-', [status(thm)], ['37', '38'])).
% 0.78/1.01  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('41', plain, ((l1_pre_topc @ sk_C)),
% 0.78/1.01      inference('demod', [status(thm)], ['39', '40'])).
% 0.78/1.01  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.78/1.01      inference('demod', [status(thm)], ['36', '41'])).
% 0.78/1.01  thf('43', plain,
% 0.78/1.01      (![X41 : $i, X42 : $i]:
% 0.78/1.01         (~ (m1_pre_topc @ X41 @ X42)
% 0.78/1.01          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.78/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.78/1.01          | ~ (l1_pre_topc @ X42))),
% 0.78/1.01      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.78/1.01  thf('44', plain,
% 0.78/1.01      ((~ (l1_pre_topc @ sk_C)
% 0.78/1.01        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/1.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['42', '43'])).
% 0.78/1.01  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 0.78/1.01      inference('demod', [status(thm)], ['39', '40'])).
% 0.78/1.01  thf('46', plain,
% 0.78/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.78/1.01      inference('demod', [status(thm)], ['44', '45'])).
% 0.78/1.01  thf('47', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i]:
% 0.78/1.01         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.78/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.01  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('sup-', [status(thm)], ['46', '47'])).
% 0.78/1.01  thf('49', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('50', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('demod', [status(thm)], ['1', '49'])).
% 0.78/1.01  thf('51', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(redefinition_r1_funct_2, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.78/1.01     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.78/1.01         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.78/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.78/1.01         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.78/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.78/1.01       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.78/1.01  thf('52', plain,
% 0.78/1.01      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.78/1.01          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.78/1.01          | ~ (v1_funct_1 @ X28)
% 0.78/1.01          | (v1_xboole_0 @ X31)
% 0.78/1.01          | (v1_xboole_0 @ X30)
% 0.78/1.01          | ~ (v1_funct_1 @ X32)
% 0.78/1.01          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.78/1.01          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.78/1.01          | (r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32)
% 0.78/1.01          | ((X28) != (X32)))),
% 0.78/1.01      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.78/1.01  thf('53', plain,
% 0.78/1.01      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.78/1.01         ((r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X32 @ X32)
% 0.78/1.01          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.78/1.01          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.78/1.01          | (v1_xboole_0 @ X30)
% 0.78/1.01          | (v1_xboole_0 @ X31)
% 0.78/1.01          | ~ (v1_funct_1 @ X32)
% 0.78/1.01          | ~ (v1_funct_2 @ X32 @ X29 @ X30)
% 0.78/1.01          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.78/1.01      inference('simplify', [status(thm)], ['52'])).
% 0.78/1.01  thf('54', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.78/1.01          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.78/1.01          | ~ (v1_funct_1 @ sk_D)
% 0.78/1.01          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01          | (v1_xboole_0 @ X0)
% 0.78/1.01          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/1.01          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.78/1.01             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.78/1.01      inference('sup-', [status(thm)], ['51', '53'])).
% 0.78/1.01  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('56', plain,
% 0.78/1.01      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('57', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.78/1.01          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.78/1.01          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01          | (v1_xboole_0 @ X0)
% 0.78/1.01          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.78/1.01             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.78/1.01      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.78/1.01  thf('58', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('59', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.78/1.01          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.78/1.01          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01          | (v1_xboole_0 @ X0)
% 0.78/1.01          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.78/1.01             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.78/1.01      inference('demod', [status(thm)], ['57', '58'])).
% 0.78/1.01  thf('60', plain,
% 0.78/1.01      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.78/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['50', '59'])).
% 0.78/1.01  thf('61', plain,
% 0.78/1.01      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('62', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('63', plain,
% 0.78/1.01      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.78/1.01      inference('demod', [status(thm)], ['61', '62'])).
% 0.78/1.01  thf('64', plain,
% 0.78/1.01      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.78/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/1.01      inference('demod', [status(thm)], ['60', '63'])).
% 0.78/1.01  thf('65', plain,
% 0.78/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/1.01        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.78/1.01      inference('simplify', [status(thm)], ['64'])).
% 0.78/1.01  thf('66', plain,
% 0.78/1.01      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.78/1.01          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('67', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('68', plain,
% 0.78/1.01      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.78/1.01          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['66', '67'])).
% 0.78/1.01  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('70', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('demod', [status(thm)], ['1', '49'])).
% 0.78/1.01  thf('71', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf(d4_tmap_1, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.78/1.01       ( ![B:$i]:
% 0.78/1.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.78/1.01             ( l1_pre_topc @ B ) ) =>
% 0.78/1.01           ( ![C:$i]:
% 0.78/1.01             ( ( ( v1_funct_1 @ C ) & 
% 0.78/1.01                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.78/1.01                 ( m1_subset_1 @
% 0.78/1.01                   C @ 
% 0.78/1.01                   ( k1_zfmisc_1 @
% 0.78/1.01                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.78/1.01               ( ![D:$i]:
% 0.78/1.01                 ( ( m1_pre_topc @ D @ A ) =>
% 0.78/1.01                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.78/1.01                     ( k2_partfun1 @
% 0.78/1.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.78/1.01                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.78/1.01  thf('72', plain,
% 0.78/1.01      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.78/1.01         ((v2_struct_0 @ X34)
% 0.78/1.01          | ~ (v2_pre_topc @ X34)
% 0.78/1.01          | ~ (l1_pre_topc @ X34)
% 0.78/1.01          | ~ (m1_pre_topc @ X35 @ X36)
% 0.78/1.01          | ((k2_tmap_1 @ X36 @ X34 @ X37 @ X35)
% 0.78/1.01              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34) @ 
% 0.78/1.01                 X37 @ (u1_struct_0 @ X35)))
% 0.78/1.01          | ~ (m1_subset_1 @ X37 @ 
% 0.78/1.01               (k1_zfmisc_1 @ 
% 0.78/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))))
% 0.78/1.01          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))
% 0.78/1.01          | ~ (v1_funct_1 @ X37)
% 0.78/1.01          | ~ (l1_pre_topc @ X36)
% 0.78/1.01          | ~ (v2_pre_topc @ X36)
% 0.78/1.01          | (v2_struct_0 @ X36))),
% 0.78/1.01      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.78/1.01  thf('73', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ X1 @ 
% 0.78/1.01             (k1_zfmisc_1 @ 
% 0.78/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.78/1.01          | (v2_struct_0 @ sk_B)
% 0.78/1.01          | ~ (v2_pre_topc @ sk_B)
% 0.78/1.01          | ~ (l1_pre_topc @ sk_B)
% 0.78/1.01          | ~ (v1_funct_1 @ X1)
% 0.78/1.01          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.78/1.01          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.78/1.01              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.78/1.01                 X1 @ (u1_struct_0 @ X2)))
% 0.78/1.01          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | (v2_struct_0 @ X0))),
% 0.78/1.01      inference('sup-', [status(thm)], ['71', '72'])).
% 0.78/1.01  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('76', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('77', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('78', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ X1 @ 
% 0.78/1.01             (k1_zfmisc_1 @ 
% 0.78/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.78/1.01          | (v2_struct_0 @ sk_B)
% 0.78/1.01          | ~ (v1_funct_1 @ X1)
% 0.78/1.01          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.78/1.01          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.78/1.01              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.78/1.01                 X1 @ (u1_struct_0 @ X2)))
% 0.78/1.01          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.78/1.01          | ~ (l1_pre_topc @ X0)
% 0.78/1.01          | ~ (v2_pre_topc @ X0)
% 0.78/1.01          | (v2_struct_0 @ X0))),
% 0.78/1.01      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.78/1.01  thf('79', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         ((v2_struct_0 @ sk_A)
% 0.78/1.01          | ~ (v2_pre_topc @ sk_A)
% 0.78/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.78/1.01          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.78/1.01          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.78/1.01              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01                 sk_D @ (u1_struct_0 @ X0)))
% 0.78/1.01          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.78/1.01          | ~ (v1_funct_1 @ sk_D)
% 0.78/1.01          | (v2_struct_0 @ sk_B))),
% 0.78/1.01      inference('sup-', [status(thm)], ['70', '78'])).
% 0.78/1.01  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('82', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(redefinition_k2_partfun1, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/1.01     ( ( ( v1_funct_1 @ C ) & 
% 0.78/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/1.01       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.78/1.01  thf('83', plain,
% 0.78/1.01      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.78/1.01         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.78/1.01          | ~ (v1_funct_1 @ X14)
% 0.78/1.01          | ((k2_partfun1 @ X15 @ X16 @ X14 @ X17) = (k7_relat_1 @ X14 @ X17)))),
% 0.78/1.01      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.78/1.01  thf('84', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.78/1.01            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.78/1.01          | ~ (v1_funct_1 @ sk_D))),
% 0.78/1.01      inference('sup-', [status(thm)], ['82', '83'])).
% 0.78/1.01  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('86', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.78/1.01           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.78/1.01      inference('demod', [status(thm)], ['84', '85'])).
% 0.78/1.01  thf('87', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('88', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.78/1.01           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.78/1.01      inference('demod', [status(thm)], ['86', '87'])).
% 0.78/1.01  thf('89', plain,
% 0.78/1.01      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.78/1.01      inference('demod', [status(thm)], ['61', '62'])).
% 0.78/1.01  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('91', plain,
% 0.78/1.01      (![X0 : $i]:
% 0.78/1.01         ((v2_struct_0 @ sk_A)
% 0.78/1.01          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.78/1.01          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.78/1.01              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.78/1.01          | (v2_struct_0 @ sk_B))),
% 0.78/1.01      inference('demod', [status(thm)], ['79', '80', '81', '88', '89', '90'])).
% 0.78/1.01  thf('92', plain,
% 0.78/1.01      (((v2_struct_0 @ sk_B)
% 0.78/1.01        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.78/1.01            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.78/1.01        | (v2_struct_0 @ sk_A))),
% 0.78/1.01      inference('sup-', [status(thm)], ['69', '91'])).
% 0.78/1.01  thf('93', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(cc2_relset_1, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i]:
% 0.78/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/1.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.78/1.01  thf('94', plain,
% 0.78/1.01      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.78/1.01         ((v4_relat_1 @ X11 @ X12)
% 0.78/1.01          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.78/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.78/1.01  thf('95', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.78/1.01      inference('sup-', [status(thm)], ['93', '94'])).
% 0.78/1.01  thf(t209_relat_1, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.78/1.01       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.78/1.01  thf('96', plain,
% 0.78/1.01      (![X6 : $i, X7 : $i]:
% 0.78/1.01         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.78/1.01          | ~ (v4_relat_1 @ X6 @ X7)
% 0.78/1.01          | ~ (v1_relat_1 @ X6))),
% 0.78/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.78/1.01  thf('97', plain,
% 0.78/1.01      ((~ (v1_relat_1 @ sk_D)
% 0.78/1.01        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['95', '96'])).
% 0.78/1.01  thf('98', plain,
% 0.78/1.01      ((m1_subset_1 @ sk_D @ 
% 0.78/1.01        (k1_zfmisc_1 @ 
% 0.78/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(cc1_relset_1, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i]:
% 0.78/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/1.01       ( v1_relat_1 @ C ) ))).
% 0.78/1.01  thf('99', plain,
% 0.78/1.01      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.78/1.01         ((v1_relat_1 @ X8)
% 0.78/1.01          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.78/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.78/1.01  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 0.78/1.01      inference('sup-', [status(thm)], ['98', '99'])).
% 0.78/1.01  thf('101', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.78/1.01      inference('demod', [status(thm)], ['97', '100'])).
% 0.78/1.01  thf('102', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.78/1.01      inference('demod', [status(thm)], ['10', '48'])).
% 0.78/1.01  thf('103', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.78/1.01      inference('demod', [status(thm)], ['101', '102'])).
% 0.78/1.01  thf('104', plain,
% 0.78/1.01      (((v2_struct_0 @ sk_B)
% 0.78/1.01        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.78/1.01        | (v2_struct_0 @ sk_A))),
% 0.78/1.01      inference('demod', [status(thm)], ['92', '103'])).
% 0.78/1.01  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('106', plain,
% 0.78/1.01      (((v2_struct_0 @ sk_A)
% 0.78/1.01        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.78/1.01      inference('clc', [status(thm)], ['104', '105'])).
% 0.78/1.01  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('108', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.78/1.01      inference('clc', [status(thm)], ['106', '107'])).
% 0.78/1.01  thf('109', plain,
% 0.78/1.01      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.78/1.01          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.78/1.01      inference('demod', [status(thm)], ['68', '108'])).
% 0.78/1.01  thf('110', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.78/1.01      inference('sup-', [status(thm)], ['65', '109'])).
% 0.78/1.01  thf(fc2_struct_0, axiom,
% 0.78/1.01    (![A:$i]:
% 0.78/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.78/1.01       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.78/1.01  thf('111', plain,
% 0.78/1.01      (![X24 : $i]:
% 0.78/1.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.78/1.01          | ~ (l1_struct_0 @ X24)
% 0.78/1.01          | (v2_struct_0 @ X24))),
% 0.78/1.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.78/1.01  thf('112', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.78/1.01      inference('sup-', [status(thm)], ['110', '111'])).
% 0.78/1.01  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf(dt_l1_pre_topc, axiom,
% 0.78/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.78/1.01  thf('114', plain,
% 0.78/1.01      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.78/1.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.78/1.01  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.78/1.01      inference('sup-', [status(thm)], ['113', '114'])).
% 0.78/1.01  thf('116', plain, ((v2_struct_0 @ sk_A)),
% 0.78/1.01      inference('demod', [status(thm)], ['112', '115'])).
% 0.78/1.01  thf('117', plain, ($false), inference('demod', [status(thm)], ['0', '116'])).
% 0.78/1.01  
% 0.78/1.01  % SZS output end Refutation
% 0.78/1.01  
% 0.86/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
