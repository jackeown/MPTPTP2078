%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hzg3HBp6eK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:39 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 656 expanded)
%              Number of leaves         :   46 ( 208 expanded)
%              Depth                    :   23
%              Number of atoms          : 1539 (16289 expanded)
%              Number of equality atoms :   33 ( 267 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X41: $i] :
      ( ( m1_pre_topc @ X41 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X44 )
      | ( r1_tarski @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
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
    ! [X41: $i] :
      ( ( m1_pre_topc @ X41 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X25: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X23 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
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

thf('22',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) @ X40 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ( m1_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X41: $i] :
      ( ( m1_pre_topc @ X41 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('48',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X44 )
      | ( r1_tarski @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
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

thf('59',plain,(
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

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('76',plain,(
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

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k2_partfun1 @ X13 @ X14 @ X12 @ X15 )
        = ( k7_relat_1 @ X12 @ X15 ) ) ) ),
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

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','94'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('97',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('99',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('100',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','55'])).

thf('110',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['97','110'])).

thf('112',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','111'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('113',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('116',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hzg3HBp6eK
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 389 iterations in 0.491s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.76/0.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.98  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.98  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.76/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.76/0.98  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.76/0.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.98  thf(t60_tmap_1, conjecture,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.98             ( l1_pre_topc @ B ) ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.76/0.98               ( ![D:$i]:
% 0.76/0.98                 ( ( ( v1_funct_1 @ D ) & 
% 0.76/0.98                     ( v1_funct_2 @
% 0.76/0.98                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.76/0.98                     ( m1_subset_1 @
% 0.76/0.98                       D @ 
% 0.76/0.98                       ( k1_zfmisc_1 @
% 0.76/0.98                         ( k2_zfmisc_1 @
% 0.76/0.98                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.76/0.98                   ( ( ( g1_pre_topc @
% 0.76/0.98                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.76/0.98                       ( g1_pre_topc @
% 0.76/0.98                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.76/0.98                     ( r1_funct_2 @
% 0.76/0.98                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.98                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.76/0.98                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i]:
% 0.76/0.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.98            ( l1_pre_topc @ A ) ) =>
% 0.76/0.98          ( ![B:$i]:
% 0.76/0.98            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.98                ( l1_pre_topc @ B ) ) =>
% 0.76/0.98              ( ![C:$i]:
% 0.76/0.98                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.76/0.98                  ( ![D:$i]:
% 0.76/0.98                    ( ( ( v1_funct_1 @ D ) & 
% 0.76/0.98                        ( v1_funct_2 @
% 0.76/0.98                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.76/0.98                        ( m1_subset_1 @
% 0.76/0.98                          D @ 
% 0.76/0.98                          ( k1_zfmisc_1 @
% 0.76/0.98                            ( k2_zfmisc_1 @
% 0.76/0.98                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.76/0.98                      ( ( ( g1_pre_topc @
% 0.76/0.98                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.76/0.98                          ( g1_pre_topc @
% 0.76/0.98                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.76/0.98                        ( r1_funct_2 @
% 0.76/0.98                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.98                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.76/0.98                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.76/0.98  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t2_tsep_1, axiom,
% 0.76/0.98    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      (![X41 : $i]: ((m1_pre_topc @ X41 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.76/0.98      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.98  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t4_tsep_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_pre_topc @ B @ A ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( m1_pre_topc @ C @ A ) =>
% 0.76/0.98               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.76/0.98                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.76/0.98         (~ (m1_pre_topc @ X42 @ X43)
% 0.76/0.98          | ~ (m1_pre_topc @ X42 @ X44)
% 0.76/0.98          | (r1_tarski @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X44))
% 0.76/0.98          | ~ (m1_pre_topc @ X44 @ X43)
% 0.76/0.98          | ~ (l1_pre_topc @ X43)
% 0.76/0.98          | ~ (v2_pre_topc @ X43))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v2_pre_topc @ sk_B)
% 0.76/0.98          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.98          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.76/0.98          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.76/0.98          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.98  thf('6', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.76/0.98          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.76/0.98          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.76/0.98  thf('9', plain,
% 0.76/0.98      ((~ (l1_pre_topc @ sk_B)
% 0.76/0.98        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.76/0.98        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '8'])).
% 0.76/0.98  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('12', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.76/0.98  thf(d10_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X0 : $i, X2 : $i]:
% 0.76/0.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.76/0.98        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.76/0.98         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X41 : $i]: ((m1_pre_topc @ X41 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.76/0.98      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.98  thf(fc6_pre_topc, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.98       ( ( v1_pre_topc @
% 0.76/0.98           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.76/0.98         ( v2_pre_topc @
% 0.76/0.98           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      (![X25 : $i]:
% 0.76/0.98         ((v2_pre_topc @ 
% 0.76/0.98           (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 0.76/0.98          | ~ (l1_pre_topc @ X25)
% 0.76/0.98          | ~ (v2_pre_topc @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.76/0.98  thf(dt_u1_pre_topc, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( l1_pre_topc @ A ) =>
% 0.76/0.98       ( m1_subset_1 @
% 0.76/0.98         ( u1_pre_topc @ A ) @ 
% 0.76/0.98         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      (![X23 : $i]:
% 0.76/0.98         ((m1_subset_1 @ (u1_pre_topc @ X23) @ 
% 0.76/0.98           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.76/0.98          | ~ (l1_pre_topc @ X23))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.76/0.98  thf(dt_g1_pre_topc, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.98       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.76/0.98         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      (![X18 : $i, X19 : $i]:
% 0.76/0.98         ((l1_pre_topc @ (g1_pre_topc @ X18 @ X19))
% 0.76/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X0)
% 0.76/0.98          | (l1_pre_topc @ 
% 0.76/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf(t12_tmap_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( l1_pre_topc @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.76/0.98               ( ( ( B ) =
% 0.76/0.98                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.76/0.98                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.76/0.98         (~ (v2_pre_topc @ X38)
% 0.76/0.98          | ~ (l1_pre_topc @ X38)
% 0.76/0.98          | ((X38) != (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39)))
% 0.76/0.98          | ~ (m1_pre_topc @ X38 @ X40)
% 0.76/0.98          | (m1_pre_topc @ X39 @ X40)
% 0.76/0.98          | ~ (l1_pre_topc @ X39)
% 0.76/0.98          | ~ (v2_pre_topc @ X39)
% 0.76/0.98          | ~ (l1_pre_topc @ X40))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X39 : $i, X40 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X40)
% 0.76/0.98          | ~ (v2_pre_topc @ X39)
% 0.76/0.98          | ~ (l1_pre_topc @ X39)
% 0.76/0.98          | (m1_pre_topc @ X39 @ X40)
% 0.76/0.98          | ~ (m1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39)) @ X40)
% 0.76/0.98          | ~ (l1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39)))
% 0.76/0.98          | ~ (v2_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39))))),
% 0.76/0.98      inference('simplify', [status(thm)], ['21'])).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (v2_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.76/0.98          | ~ (m1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.76/0.98          | (m1_pre_topc @ X0 @ X1)
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['20', '22'])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X1)
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | (m1_pre_topc @ X0 @ X1)
% 0.76/0.98          | ~ (m1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.76/0.98          | ~ (v2_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.76/0.98          | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['23'])).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (m1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.76/0.98          | (m1_pre_topc @ X0 @ X1)
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['17', '24'])).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X1)
% 0.76/0.98          | (m1_pre_topc @ X0 @ X1)
% 0.76/0.98          | ~ (m1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (v2_pre_topc @ X0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['25'])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ 
% 0.76/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | (m1_pre_topc @ X0 @ 
% 0.76/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.76/0.98          | ~ (l1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['16', '26'])).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((m1_pre_topc @ X0 @ 
% 0.76/0.98           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ 
% 0.76/0.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.76/0.98      inference('simplify', [status(thm)], ['27'])).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      ((~ (l1_pre_topc @ 
% 0.76/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.76/0.98        | ~ (v2_pre_topc @ sk_B)
% 0.76/0.98        | ~ (l1_pre_topc @ sk_B)
% 0.76/0.98        | (m1_pre_topc @ sk_B @ 
% 0.76/0.98           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['15', '28'])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.76/0.98         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X0)
% 0.76/0.98          | (l1_pre_topc @ 
% 0.76/0.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      (((l1_pre_topc @ 
% 0.76/0.98         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.76/0.98        | ~ (l1_pre_topc @ sk_B))),
% 0.76/0.98      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.98  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      ((l1_pre_topc @ 
% 0.76/0.98        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.76/0.98      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.98  thf('35', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.76/0.98         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      ((m1_pre_topc @ sk_B @ 
% 0.76/0.98        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.76/0.98      inference('demod', [status(thm)], ['29', '34', '35', '36', '37'])).
% 0.76/0.98  thf(t59_pre_topc, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( l1_pre_topc @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_pre_topc @
% 0.76/0.98             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.76/0.98           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i]:
% 0.76/0.98         (~ (m1_pre_topc @ X26 @ 
% 0.76/0.98             (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.76/0.98          | (m1_pre_topc @ X26 @ X27)
% 0.76/0.98          | ~ (l1_pre_topc @ X27))),
% 0.76/0.98      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.76/0.98  thf('40', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(dt_m1_pre_topc, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( l1_pre_topc @ A ) =>
% 0.76/0.98       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.76/0.98  thf('42', plain,
% 0.76/0.98      (![X21 : $i, X22 : $i]:
% 0.76/0.98         (~ (m1_pre_topc @ X21 @ X22)
% 0.76/0.98          | (l1_pre_topc @ X21)
% 0.76/0.98          | ~ (l1_pre_topc @ X22))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.76/0.98  thf('43', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.98  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['43', '44'])).
% 0.76/0.98  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['40', '45'])).
% 0.76/0.98  thf('47', plain,
% 0.76/0.98      (![X41 : $i]: ((m1_pre_topc @ X41 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.76/0.98      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.98  thf('48', plain,
% 0.76/0.98      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.76/0.98         (~ (m1_pre_topc @ X42 @ X43)
% 0.76/0.98          | ~ (m1_pre_topc @ X42 @ X44)
% 0.76/0.98          | (r1_tarski @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X44))
% 0.76/0.98          | ~ (m1_pre_topc @ X44 @ X43)
% 0.76/0.98          | ~ (l1_pre_topc @ X43)
% 0.76/0.98          | ~ (v2_pre_topc @ X43))),
% 0.76/0.98      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X0)
% 0.76/0.98          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.98          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.76/0.98          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.98  thf('50', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (m1_pre_topc @ X0 @ X1)
% 0.76/0.98          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.76/0.98          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.98          | ~ (v2_pre_topc @ X0)
% 0.76/0.98          | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['49'])).
% 0.76/0.98  thf('51', plain,
% 0.76/0.98      ((~ (l1_pre_topc @ sk_B)
% 0.76/0.98        | ~ (v2_pre_topc @ sk_B)
% 0.76/0.98        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.76/0.98        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['46', '50'])).
% 0.76/0.98  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('53', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('55', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.76/0.98  thf('56', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['14', '55'])).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('demod', [status(thm)], ['1', '56'])).
% 0.76/0.98  thf('58', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_r1_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.76/0.98     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.76/0.98         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.76/0.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.98         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.76/0.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.76/0.98       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.76/0.98  thf('59', plain,
% 0.76/0.98      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.76/0.98          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.76/0.98          | ~ (v1_funct_1 @ X28)
% 0.76/0.98          | (v1_xboole_0 @ X31)
% 0.76/0.98          | (v1_xboole_0 @ X30)
% 0.76/0.98          | ~ (v1_funct_1 @ X32)
% 0.76/0.98          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.76/0.98          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.76/0.98          | (r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32)
% 0.76/0.98          | ((X28) != (X32)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.76/0.98  thf('60', plain,
% 0.76/0.98      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.98         ((r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X32 @ X32)
% 0.76/0.98          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.76/0.98          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.76/0.98          | (v1_xboole_0 @ X30)
% 0.76/0.98          | (v1_xboole_0 @ X31)
% 0.76/0.98          | ~ (v1_funct_1 @ X32)
% 0.76/0.98          | ~ (v1_funct_2 @ X32 @ X29 @ X30)
% 0.76/0.98          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.76/0.98      inference('simplify', [status(thm)], ['59'])).
% 0.76/0.98  thf('61', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.76/0.98          | ~ (v1_funct_1 @ sk_D)
% 0.76/0.98          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.98             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['58', '60'])).
% 0.76/0.98  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('63', plain,
% 0.76/0.98      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('64', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.76/0.98          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.98             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.76/0.98  thf('65', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['14', '55'])).
% 0.76/0.98  thf('66', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.76/0.98          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.76/0.98          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | (v1_xboole_0 @ X0)
% 0.76/0.98          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.76/0.98             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['64', '65'])).
% 0.76/0.98  thf('67', plain,
% 0.76/0.98      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.76/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['57', '66'])).
% 0.76/0.98  thf('68', plain,
% 0.76/0.98      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('69', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['14', '55'])).
% 0.76/0.98  thf('70', plain,
% 0.76/0.98      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('71', plain,
% 0.76/0.98      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.76/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.98      inference('demod', [status(thm)], ['67', '70'])).
% 0.76/0.98  thf('72', plain,
% 0.76/0.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.76/0.98      inference('simplify', [status(thm)], ['71'])).
% 0.76/0.98  thf('73', plain,
% 0.76/0.98      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.76/0.98          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('75', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(d4_tmap_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.98             ( l1_pre_topc @ B ) ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.98                 ( m1_subset_1 @
% 0.76/0.98                   C @ 
% 0.76/0.98                   ( k1_zfmisc_1 @
% 0.76/0.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.98               ( ![D:$i]:
% 0.76/0.98                 ( ( m1_pre_topc @ D @ A ) =>
% 0.76/0.98                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.76/0.98                     ( k2_partfun1 @
% 0.76/0.98                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.76/0.98                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.98  thf('76', plain,
% 0.76/0.98      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X34)
% 0.76/0.98          | ~ (v2_pre_topc @ X34)
% 0.76/0.98          | ~ (l1_pre_topc @ X34)
% 0.76/0.98          | ~ (m1_pre_topc @ X35 @ X36)
% 0.76/0.98          | ((k2_tmap_1 @ X36 @ X34 @ X37 @ X35)
% 0.76/0.98              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34) @ 
% 0.76/0.98                 X37 @ (u1_struct_0 @ X35)))
% 0.76/0.98          | ~ (m1_subset_1 @ X37 @ 
% 0.76/0.98               (k1_zfmisc_1 @ 
% 0.76/0.98                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))))
% 0.76/0.98          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))
% 0.76/0.98          | ~ (v1_funct_1 @ X37)
% 0.76/0.98          | ~ (l1_pre_topc @ X36)
% 0.76/0.98          | ~ (v2_pre_topc @ X36)
% 0.76/0.98          | (v2_struct_0 @ X36))),
% 0.76/0.98      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.76/0.98  thf('77', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.98          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.98          | ~ (v1_funct_1 @ sk_D)
% 0.76/0.98          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.76/0.98              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98                 sk_D @ (u1_struct_0 @ X0)))
% 0.76/0.98          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.76/0.98          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['75', '76'])).
% 0.76/0.98  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('81', plain,
% 0.76/0.98      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('82', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k2_partfun1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.98       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.76/0.98  thf('83', plain,
% 0.76/0.98      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.76/0.98          | ~ (v1_funct_1 @ X12)
% 0.76/0.98          | ((k2_partfun1 @ X13 @ X14 @ X12 @ X15) = (k7_relat_1 @ X12 @ X15)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.76/0.98  thf('84', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.76/0.98            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.76/0.98          | ~ (v1_funct_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['82', '83'])).
% 0.76/0.98  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('86', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.76/0.98           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['84', '85'])).
% 0.76/0.98  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('89', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.76/0.98              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.76/0.98          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)],
% 0.76/0.98                ['77', '78', '79', '80', '81', '86', '87', '88'])).
% 0.76/0.98  thf('90', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_A)
% 0.76/0.98        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.76/0.98            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['74', '89'])).
% 0.76/0.98  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('92', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.76/0.98            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.76/0.98      inference('clc', [status(thm)], ['90', '91'])).
% 0.76/0.98  thf('93', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('94', plain,
% 0.76/0.98      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.76/0.98         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.76/0.98      inference('clc', [status(thm)], ['92', '93'])).
% 0.76/0.98  thf('95', plain,
% 0.76/0.98      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.76/0.98          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.76/0.98      inference('demod', [status(thm)], ['73', '94'])).
% 0.76/0.98  thf('96', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['14', '55'])).
% 0.76/0.98  thf('97', plain,
% 0.76/0.98      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.76/0.98          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.76/0.98      inference('demod', [status(thm)], ['95', '96'])).
% 0.76/0.98  thf('98', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.98  thf('99', plain,
% 0.76/0.98      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.98         ((v4_relat_1 @ X9 @ X10)
% 0.76/0.98          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('100', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['98', '99'])).
% 0.76/0.98  thf(t209_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.98       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.76/0.98  thf('101', plain,
% 0.76/0.98      (![X7 : $i, X8 : $i]:
% 0.76/0.98         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.76/0.98          | ~ (v4_relat_1 @ X7 @ X8)
% 0.76/0.98          | ~ (v1_relat_1 @ X7))),
% 0.76/0.98      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.98  thf('102', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_D)
% 0.76/0.98        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['100', '101'])).
% 0.76/0.98  thf('103', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.98  thf('104', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.76/0.98          | (v1_relat_1 @ X3)
% 0.76/0.98          | ~ (v1_relat_1 @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('105', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ 
% 0.76/0.98           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.76/0.98        | (v1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['103', '104'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('106', plain,
% 0.76/0.98      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['105', '106'])).
% 0.76/0.98  thf('108', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.76/0.98      inference('demod', [status(thm)], ['102', '107'])).
% 0.76/0.98  thf('109', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['14', '55'])).
% 0.76/0.98  thf('110', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.76/0.98      inference('demod', [status(thm)], ['108', '109'])).
% 0.76/0.98  thf('111', plain,
% 0.76/0.98      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['97', '110'])).
% 0.76/0.98  thf('112', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('clc', [status(thm)], ['72', '111'])).
% 0.76/0.98  thf(fc2_struct_0, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.98       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.98  thf('113', plain,
% 0.76/0.98      (![X24 : $i]:
% 0.76/0.98         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.76/0.98          | ~ (l1_struct_0 @ X24)
% 0.76/0.98          | (v2_struct_0 @ X24))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.76/0.98  thf('114', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['112', '113'])).
% 0.76/0.98  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(dt_l1_pre_topc, axiom,
% 0.76/0.98    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.76/0.98  thf('116', plain,
% 0.76/0.98      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['115', '116'])).
% 0.76/0.98  thf('118', plain, ((v2_struct_0 @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['114', '117'])).
% 0.76/0.98  thf('119', plain, ($false), inference('demod', [status(thm)], ['0', '118'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
