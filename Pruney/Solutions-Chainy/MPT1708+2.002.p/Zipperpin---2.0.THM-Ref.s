%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kXPlZOaR5o

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:12 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 344 expanded)
%              Number of leaves         :   36 ( 108 expanded)
%              Depth                    :   32
%              Number of atoms          : 1763 (7076 expanded)
%              Number of equality atoms :   38 ( 267 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t17_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                   => ( ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                      & ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ~ ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                     => ( ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                        & ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( r1_tsep_1 @ X26 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( v1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ( X29
       != ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
      | ( ( u1_struct_0 @ X29 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) @ X27 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
      | ( r1_tsep_1 @ X26 @ X28 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t38_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X24 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_tops_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X22 @ X21 ) )
        = X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','52','57'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','61'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) )
      | ( X35 != sk_D )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( X36 != sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X36: $i] :
        ( ( X36 != sk_D )
        | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ! [X36: $i] :
        ( ( X36 != sk_D )
        | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) )
   <= ! [X36: $i] :
        ( ( X36 != sk_D )
        | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('84',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,
    ( ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,
    ( ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
   <= ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ~ ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ! [X36: $i] :
        ( ( X36 != sk_D )
        | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ! [X35: $i] :
        ( ( X35 != sk_D )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('116',plain,(
    ! [X36: $i] :
      ( ( X36 != sk_D )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['81','116'])).

thf('118',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','117'])).

thf('119',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['0','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kXPlZOaR5o
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:58:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.07/2.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.07/2.26  % Solved by: fo/fo7.sh
% 2.07/2.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.07/2.26  % done 1000 iterations in 1.795s
% 2.07/2.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.07/2.26  % SZS output start Refutation
% 2.07/2.26  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 2.07/2.26  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.07/2.26  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.07/2.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.07/2.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.07/2.26  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.07/2.26  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 2.07/2.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.07/2.26  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.07/2.26  thf(sk_B_type, type, sk_B: $i).
% 2.07/2.26  thf(sk_A_type, type, sk_A: $i).
% 2.07/2.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.07/2.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.07/2.26  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 2.07/2.26  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.07/2.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.07/2.26  thf(sk_D_type, type, sk_D: $i).
% 2.07/2.26  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.07/2.26  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.07/2.26  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.07/2.26  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.07/2.26  thf(t17_tmap_1, conjecture,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.07/2.26       ( ![B:$i]:
% 2.07/2.26         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.07/2.26           ( ![C:$i]:
% 2.07/2.26             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.07/2.26               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 2.07/2.26                 ( ![D:$i]:
% 2.07/2.26                   ( ( m1_subset_1 @
% 2.07/2.26                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 2.07/2.26                     ( ( ?[E:$i]:
% 2.07/2.26                         ( ( ( E ) = ( D ) ) & 
% 2.07/2.26                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 2.07/2.26                       ( ?[E:$i]:
% 2.07/2.26                         ( ( ( E ) = ( D ) ) & 
% 2.07/2.26                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.07/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.07/2.26    (~( ![A:$i]:
% 2.07/2.26        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.07/2.26            ( l1_pre_topc @ A ) ) =>
% 2.07/2.26          ( ![B:$i]:
% 2.07/2.26            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.07/2.26              ( ![C:$i]:
% 2.07/2.26                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.07/2.26                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 2.07/2.26                    ( ![D:$i]:
% 2.07/2.26                      ( ( m1_subset_1 @
% 2.07/2.26                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 2.07/2.26                        ( ( ?[E:$i]:
% 2.07/2.26                            ( ( ( E ) = ( D ) ) & 
% 2.07/2.26                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 2.07/2.26                          ( ?[E:$i]:
% 2.07/2.26                            ( ( ( E ) = ( D ) ) & 
% 2.07/2.26                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.07/2.26    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 2.07/2.26  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf(dt_k2_tsep_1, axiom,
% 2.07/2.26    (![A:$i,B:$i,C:$i]:
% 2.07/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 2.07/2.26         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 2.07/2.26         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.07/2.26       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 2.07/2.26         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 2.07/2.26         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 2.07/2.26  thf('3', plain,
% 2.07/2.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X30 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X30)
% 2.07/2.26          | ~ (l1_pre_topc @ X31)
% 2.07/2.26          | (v2_struct_0 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X32)
% 2.07/2.26          | ~ (m1_pre_topc @ X32 @ X31)
% 2.07/2.26          | (m1_pre_topc @ (k2_tsep_1 @ X31 @ X30 @ X32) @ X31))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 2.07/2.26  thf('4', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 2.07/2.26          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ X0)
% 2.07/2.26          | (v2_struct_0 @ sk_A)
% 2.07/2.26          | ~ (l1_pre_topc @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('sup-', [status(thm)], ['2', '3'])).
% 2.07/2.26  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('6', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 2.07/2.26          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ X0)
% 2.07/2.26          | (v2_struct_0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('demod', [status(thm)], ['4', '5'])).
% 2.07/2.26  thf('7', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 2.07/2.26      inference('sup-', [status(thm)], ['1', '6'])).
% 2.07/2.26  thf(dt_m1_pre_topc, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( l1_pre_topc @ A ) =>
% 2.07/2.26       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.07/2.26  thf('8', plain,
% 2.07/2.26      (![X18 : $i, X19 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X18 @ X19)
% 2.07/2.26          | (l1_pre_topc @ X18)
% 2.07/2.26          | ~ (l1_pre_topc @ X19))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.07/2.26  thf('9', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | ~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['7', '8'])).
% 2.07/2.26  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('11', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('demod', [status(thm)], ['9', '10'])).
% 2.07/2.26  thf(dt_l1_pre_topc, axiom,
% 2.07/2.26    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.07/2.26  thf('12', plain,
% 2.07/2.26      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.07/2.26  thf('13', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['11', '12'])).
% 2.07/2.26  thf('14', plain,
% 2.07/2.26      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf(d2_subset_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( ( v1_xboole_0 @ A ) =>
% 2.07/2.26         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.07/2.26       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.07/2.26         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.07/2.26  thf('15', plain,
% 2.07/2.26      (![X8 : $i, X9 : $i]:
% 2.07/2.26         (~ (m1_subset_1 @ X8 @ X9)
% 2.07/2.26          | (r2_hidden @ X8 @ X9)
% 2.07/2.26          | (v1_xboole_0 @ X9))),
% 2.07/2.26      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.07/2.26  thf('16', plain,
% 2.07/2.26      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.07/2.26        | (r2_hidden @ sk_D @ 
% 2.07/2.26           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['14', '15'])).
% 2.07/2.26  thf('17', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('19', plain,
% 2.07/2.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X30 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X30)
% 2.07/2.26          | ~ (l1_pre_topc @ X31)
% 2.07/2.26          | (v2_struct_0 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X32)
% 2.07/2.26          | ~ (m1_pre_topc @ X32 @ X31)
% 2.07/2.26          | (v1_pre_topc @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 2.07/2.26  thf('20', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 2.07/2.26          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ X0)
% 2.07/2.26          | (v2_struct_0 @ sk_A)
% 2.07/2.26          | ~ (l1_pre_topc @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('sup-', [status(thm)], ['18', '19'])).
% 2.07/2.26  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('22', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 2.07/2.26          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ X0)
% 2.07/2.26          | (v2_struct_0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('demod', [status(thm)], ['20', '21'])).
% 2.07/2.26  thf('23', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['17', '22'])).
% 2.07/2.26  thf('24', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 2.07/2.26      inference('sup-', [status(thm)], ['1', '6'])).
% 2.07/2.26  thf(d5_tsep_1, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.07/2.26       ( ![B:$i]:
% 2.07/2.26         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.07/2.26           ( ![C:$i]:
% 2.07/2.26             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.07/2.26               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 2.07/2.26                 ( ![D:$i]:
% 2.07/2.26                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 2.07/2.26                       ( m1_pre_topc @ D @ A ) ) =>
% 2.07/2.26                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 2.07/2.26                       ( ( u1_struct_0 @ D ) =
% 2.07/2.26                         ( k3_xboole_0 @
% 2.07/2.26                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.07/2.26  thf('25', plain,
% 2.07/2.26      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.07/2.26         ((v2_struct_0 @ X26)
% 2.07/2.26          | ~ (m1_pre_topc @ X26 @ X27)
% 2.07/2.26          | (r1_tsep_1 @ X26 @ X28)
% 2.07/2.26          | (v2_struct_0 @ X29)
% 2.07/2.26          | ~ (v1_pre_topc @ X29)
% 2.07/2.26          | ~ (m1_pre_topc @ X29 @ X27)
% 2.07/2.26          | ((X29) != (k2_tsep_1 @ X27 @ X26 @ X28))
% 2.07/2.26          | ((u1_struct_0 @ X29)
% 2.07/2.26              = (k3_xboole_0 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28)))
% 2.07/2.26          | ~ (m1_pre_topc @ X28 @ X27)
% 2.07/2.26          | (v2_struct_0 @ X28)
% 2.07/2.26          | ~ (l1_pre_topc @ X27)
% 2.07/2.26          | (v2_struct_0 @ X27))),
% 2.07/2.26      inference('cnf', [status(esa)], [d5_tsep_1])).
% 2.07/2.26  thf('26', plain,
% 2.07/2.26      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.07/2.26         ((v2_struct_0 @ X27)
% 2.07/2.26          | ~ (l1_pre_topc @ X27)
% 2.07/2.26          | (v2_struct_0 @ X28)
% 2.07/2.26          | ~ (m1_pre_topc @ X28 @ X27)
% 2.07/2.26          | ((u1_struct_0 @ (k2_tsep_1 @ X27 @ X26 @ X28))
% 2.07/2.26              = (k3_xboole_0 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28)))
% 2.07/2.26          | ~ (m1_pre_topc @ (k2_tsep_1 @ X27 @ X26 @ X28) @ X27)
% 2.07/2.26          | ~ (v1_pre_topc @ (k2_tsep_1 @ X27 @ X26 @ X28))
% 2.07/2.26          | (v2_struct_0 @ (k2_tsep_1 @ X27 @ X26 @ X28))
% 2.07/2.26          | (r1_tsep_1 @ X26 @ X28)
% 2.07/2.26          | ~ (m1_pre_topc @ X26 @ X27)
% 2.07/2.26          | (v2_struct_0 @ X26))),
% 2.07/2.26      inference('simplify', [status(thm)], ['25'])).
% 2.07/2.26  thf('27', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | ~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_A))),
% 2.07/2.26      inference('sup-', [status(thm)], ['24', '26'])).
% 2.07/2.26  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('29', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('31', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A))),
% 2.07/2.26      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 2.07/2.26  thf('32', plain,
% 2.07/2.26      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['31'])).
% 2.07/2.26  thf('33', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['23', '32'])).
% 2.07/2.26  thf('34', plain,
% 2.07/2.26      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['33'])).
% 2.07/2.26  thf('35', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf(t1_tsep_1, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( l1_pre_topc @ A ) =>
% 2.07/2.26       ( ![B:$i]:
% 2.07/2.26         ( ( m1_pre_topc @ B @ A ) =>
% 2.07/2.26           ( m1_subset_1 @
% 2.07/2.26             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.07/2.26  thf('36', plain,
% 2.07/2.26      (![X33 : $i, X34 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X33 @ X34)
% 2.07/2.26          | (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 2.07/2.26             (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.07/2.26          | ~ (l1_pre_topc @ X34))),
% 2.07/2.26      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.07/2.26  thf('37', plain,
% 2.07/2.26      ((~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.07/2.26           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['35', '36'])).
% 2.07/2.26  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('39', plain,
% 2.07/2.26      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.07/2.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['37', '38'])).
% 2.07/2.26  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('41', plain,
% 2.07/2.26      (![X33 : $i, X34 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X33 @ X34)
% 2.07/2.26          | (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 2.07/2.26             (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.07/2.26          | ~ (l1_pre_topc @ X34))),
% 2.07/2.26      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.07/2.26  thf('42', plain,
% 2.07/2.26      ((~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 2.07/2.26           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['40', '41'])).
% 2.07/2.26  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('44', plain,
% 2.07/2.26      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 2.07/2.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['42', '43'])).
% 2.07/2.26  thf(t38_tops_2, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( l1_pre_topc @ A ) =>
% 2.07/2.26       ( ![B:$i]:
% 2.07/2.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.07/2.26           ( ![C:$i]:
% 2.07/2.26             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.07/2.26               ( m1_subset_1 @
% 2.07/2.26                 ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 2.07/2.26                 ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 2.07/2.26  thf('45', plain,
% 2.07/2.26      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.07/2.26         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.07/2.26          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25) @ 
% 2.07/2.26             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X24 @ X25))))
% 2.07/2.26          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.07/2.26          | ~ (l1_pre_topc @ X24))),
% 2.07/2.26      inference('cnf', [status(esa)], [t38_tops_2])).
% 2.07/2.26  thf('46', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (~ (l1_pre_topc @ sk_A)
% 2.07/2.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.07/2.26          | (m1_subset_1 @ 
% 2.07/2.26             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0) @ 
% 2.07/2.26             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['44', '45'])).
% 2.07/2.26  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('48', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.07/2.26          | (m1_subset_1 @ 
% 2.07/2.26             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0) @ 
% 2.07/2.26             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 2.07/2.26      inference('demod', [status(thm)], ['46', '47'])).
% 2.07/2.26  thf('49', plain,
% 2.07/2.26      ((m1_subset_1 @ 
% 2.07/2.26        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.07/2.26         (u1_struct_0 @ sk_C_1)) @ 
% 2.07/2.26        (k1_zfmisc_1 @ 
% 2.07/2.26         (u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['39', '48'])).
% 2.07/2.26  thf('50', plain,
% 2.07/2.26      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.07/2.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['37', '38'])).
% 2.07/2.26  thf(redefinition_k9_subset_1, axiom,
% 2.07/2.26    (![A:$i,B:$i,C:$i]:
% 2.07/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.07/2.26       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.07/2.26  thf('51', plain,
% 2.07/2.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.07/2.26         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 2.07/2.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.07/2.26      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.07/2.26  thf('52', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26           = (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['50', '51'])).
% 2.07/2.26  thf('53', plain,
% 2.07/2.26      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.07/2.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.07/2.26      inference('demod', [status(thm)], ['37', '38'])).
% 2.07/2.26  thf(t29_pre_topc, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( l1_pre_topc @ A ) =>
% 2.07/2.26       ( ![B:$i]:
% 2.07/2.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.07/2.26           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 2.07/2.26  thf('54', plain,
% 2.07/2.26      (![X21 : $i, X22 : $i]:
% 2.07/2.26         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.07/2.26          | ((u1_struct_0 @ (k1_pre_topc @ X22 @ X21)) = (X21))
% 2.07/2.26          | ~ (l1_pre_topc @ X22))),
% 2.07/2.26      inference('cnf', [status(esa)], [t29_pre_topc])).
% 2.07/2.26  thf('55', plain,
% 2.07/2.26      ((~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26            = (u1_struct_0 @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['53', '54'])).
% 2.07/2.26  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('57', plain,
% 2.07/2.26      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26         = (u1_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('demod', [status(thm)], ['55', '56'])).
% 2.07/2.26  thf('58', plain,
% 2.07/2.26      ((m1_subset_1 @ 
% 2.07/2.26        (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)) @ 
% 2.07/2.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 2.07/2.26      inference('demod', [status(thm)], ['49', '52', '57'])).
% 2.07/2.26  thf(l3_subset_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.07/2.26       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.07/2.26  thf('59', plain,
% 2.07/2.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.07/2.26         (~ (r2_hidden @ X11 @ X12)
% 2.07/2.26          | (r2_hidden @ X11 @ X13)
% 2.07/2.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 2.07/2.26      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.07/2.26  thf('60', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26          | ~ (r2_hidden @ X0 @ 
% 2.07/2.26               (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['58', '59'])).
% 2.07/2.26  thf('61', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (~ (r2_hidden @ X0 @ 
% 2.07/2.26             (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.07/2.26          | (v2_struct_0 @ sk_C_1)
% 2.07/2.26          | (v2_struct_0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ sk_B)
% 2.07/2.26          | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['34', '60'])).
% 2.07/2.26  thf('62', plain,
% 2.07/2.26      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('sup-', [status(thm)], ['16', '61'])).
% 2.07/2.26  thf(fc2_struct_0, axiom,
% 2.07/2.26    (![A:$i]:
% 2.07/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.07/2.26       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.07/2.26  thf('63', plain,
% 2.07/2.26      (![X20 : $i]:
% 2.07/2.26         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 2.07/2.26          | ~ (l1_struct_0 @ X20)
% 2.07/2.26          | (v2_struct_0 @ X20))),
% 2.07/2.26      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.07/2.26  thf('64', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['62', '63'])).
% 2.07/2.26  thf('65', plain,
% 2.07/2.26      ((~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['64'])).
% 2.07/2.26  thf('66', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['13', '65'])).
% 2.07/2.26  thf('67', plain,
% 2.07/2.26      (((r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['66'])).
% 2.07/2.26  thf('68', plain,
% 2.07/2.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X30 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X30)
% 2.07/2.26          | ~ (l1_pre_topc @ X31)
% 2.07/2.26          | (v2_struct_0 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X32)
% 2.07/2.26          | ~ (m1_pre_topc @ X32 @ X31)
% 2.07/2.26          | ~ (v2_struct_0 @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 2.07/2.26  thf('69', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | ~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 2.07/2.26      inference('sup-', [status(thm)], ['67', '68'])).
% 2.07/2.26  thf('70', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('72', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('73', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 2.07/2.26  thf('74', plain,
% 2.07/2.26      (((r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['73'])).
% 2.07/2.26  thf('75', plain,
% 2.07/2.26      (![X8 : $i, X9 : $i]:
% 2.07/2.26         (~ (r2_hidden @ X8 @ X9)
% 2.07/2.26          | (m1_subset_1 @ X8 @ X9)
% 2.07/2.26          | (v1_xboole_0 @ X9))),
% 2.07/2.26      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.07/2.26  thf(t7_boole, axiom,
% 2.07/2.26    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 2.07/2.26  thf('76', plain,
% 2.07/2.26      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (v1_xboole_0 @ X7))),
% 2.07/2.26      inference('cnf', [status(esa)], [t7_boole])).
% 2.07/2.26  thf('77', plain,
% 2.07/2.26      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 2.07/2.26      inference('clc', [status(thm)], ['75', '76'])).
% 2.07/2.26  thf('78', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['74', '77'])).
% 2.07/2.26  thf('79', plain,
% 2.07/2.26      (![X35 : $i, X36 : $i]:
% 2.07/2.26         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B))
% 2.07/2.26          | ((X35) != (sk_D))
% 2.07/2.26          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_C_1))
% 2.07/2.26          | ((X36) != (sk_D)))),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('80', plain,
% 2.07/2.26      ((![X36 : $i]:
% 2.07/2.26          (((X36) != (sk_D)) | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_C_1))))
% 2.07/2.26         <= ((![X36 : $i]:
% 2.07/2.26                (((X36) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_C_1)))))),
% 2.07/2.26      inference('split', [status(esa)], ['79'])).
% 2.07/2.26  thf('81', plain,
% 2.07/2.26      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26         <= ((![X36 : $i]:
% 2.07/2.26                (((X36) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_C_1)))))),
% 2.07/2.26      inference('simplify', [status(thm)], ['80'])).
% 2.07/2.26  thf('82', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['11', '12'])).
% 2.07/2.26  thf('83', plain,
% 2.07/2.26      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.07/2.26        | (r2_hidden @ sk_D @ 
% 2.07/2.26           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['14', '15'])).
% 2.07/2.26  thf('84', plain,
% 2.07/2.26      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['33'])).
% 2.07/2.26  thf(t17_xboole_1, axiom,
% 2.07/2.26    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.07/2.26  thf('85', plain,
% 2.07/2.26      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 2.07/2.26      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.07/2.26  thf(d3_tarski, axiom,
% 2.07/2.26    (![A:$i,B:$i]:
% 2.07/2.26     ( ( r1_tarski @ A @ B ) <=>
% 2.07/2.26       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.07/2.26  thf('86', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         (~ (r2_hidden @ X0 @ X1)
% 2.07/2.26          | (r2_hidden @ X0 @ X2)
% 2.07/2.26          | ~ (r1_tarski @ X1 @ X2))),
% 2.07/2.26      inference('cnf', [status(esa)], [d3_tarski])).
% 2.07/2.26  thf('87', plain,
% 2.07/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.07/2.26         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['85', '86'])).
% 2.07/2.26  thf('88', plain,
% 2.07/2.26      (![X0 : $i]:
% 2.07/2.26         (~ (r2_hidden @ X0 @ 
% 2.07/2.26             (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.07/2.26          | (v2_struct_0 @ sk_C_1)
% 2.07/2.26          | (v2_struct_0 @ sk_A)
% 2.07/2.26          | (v2_struct_0 @ sk_B)
% 2.07/2.26          | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['84', '87'])).
% 2.07/2.26  thf('89', plain,
% 2.07/2.26      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('sup-', [status(thm)], ['83', '88'])).
% 2.07/2.26  thf('90', plain,
% 2.07/2.26      (![X20 : $i]:
% 2.07/2.26         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 2.07/2.26          | ~ (l1_struct_0 @ X20)
% 2.07/2.26          | (v2_struct_0 @ X20))),
% 2.07/2.26      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.07/2.26  thf('91', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['89', '90'])).
% 2.07/2.26  thf('92', plain,
% 2.07/2.26      ((~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['91'])).
% 2.07/2.26  thf('93', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['82', '92'])).
% 2.07/2.26  thf('94', plain,
% 2.07/2.26      (((r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['93'])).
% 2.07/2.26  thf('95', plain,
% 2.07/2.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.07/2.26         (~ (m1_pre_topc @ X30 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X30)
% 2.07/2.26          | ~ (l1_pre_topc @ X31)
% 2.07/2.26          | (v2_struct_0 @ X31)
% 2.07/2.26          | (v2_struct_0 @ X32)
% 2.07/2.26          | ~ (m1_pre_topc @ X32 @ X31)
% 2.07/2.26          | ~ (v2_struct_0 @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 2.07/2.26      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 2.07/2.26  thf('96', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | ~ (l1_pre_topc @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 2.07/2.26      inference('sup-', [status(thm)], ['94', '95'])).
% 2.07/2.26  thf('97', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('99', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('100', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | (v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 2.07/2.26  thf('101', plain,
% 2.07/2.26      (((r2_hidden @ sk_D @ (u1_struct_0 @ sk_B))
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simplify', [status(thm)], ['100'])).
% 2.07/2.26  thf('102', plain,
% 2.07/2.26      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 2.07/2.26      inference('clc', [status(thm)], ['75', '76'])).
% 2.07/2.26  thf('103', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 2.07/2.26      inference('sup-', [status(thm)], ['101', '102'])).
% 2.07/2.26  thf('104', plain,
% 2.07/2.26      ((![X35 : $i]:
% 2.07/2.26          (((X35) != (sk_D)) | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B))))
% 2.07/2.26         <= ((![X35 : $i]:
% 2.07/2.26                (((X35) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B)))))),
% 2.07/2.26      inference('split', [status(esa)], ['79'])).
% 2.07/2.26  thf('105', plain,
% 2.07/2.26      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))
% 2.07/2.26         <= ((![X35 : $i]:
% 2.07/2.26                (((X35) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B)))))),
% 2.07/2.26      inference('simplify', [status(thm)], ['104'])).
% 2.07/2.26  thf('106', plain,
% 2.07/2.26      ((((r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26         | (v2_struct_0 @ sk_B)
% 2.07/2.26         | (v2_struct_0 @ sk_A)
% 2.07/2.26         | (v2_struct_0 @ sk_C_1)))
% 2.07/2.26         <= ((![X35 : $i]:
% 2.07/2.26                (((X35) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B)))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['103', '105'])).
% 2.07/2.26  thf('107', plain, (~ (r1_tsep_1 @ sk_B @ sk_C_1)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('108', plain,
% 2.07/2.26      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 2.07/2.26         <= ((![X35 : $i]:
% 2.07/2.26                (((X35) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B)))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['106', '107'])).
% 2.07/2.26  thf('109', plain, (~ (v2_struct_0 @ sk_C_1)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('110', plain,
% 2.07/2.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 2.07/2.26         <= ((![X35 : $i]:
% 2.07/2.26                (((X35) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B)))))),
% 2.07/2.26      inference('clc', [status(thm)], ['108', '109'])).
% 2.07/2.26  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('112', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_A))
% 2.07/2.26         <= ((![X35 : $i]:
% 2.07/2.26                (((X35) != (sk_D))
% 2.07/2.26                 | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B)))))),
% 2.07/2.26      inference('clc', [status(thm)], ['110', '111'])).
% 2.07/2.26  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('114', plain,
% 2.07/2.26      (~
% 2.07/2.26       (![X35 : $i]:
% 2.07/2.26          (((X35) != (sk_D)) | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B))))),
% 2.07/2.26      inference('sup-', [status(thm)], ['112', '113'])).
% 2.07/2.26  thf('115', plain,
% 2.07/2.26      ((![X36 : $i]:
% 2.07/2.26          (((X36) != (sk_D)) | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_C_1)))) | 
% 2.07/2.26       (![X35 : $i]:
% 2.07/2.26          (((X35) != (sk_D)) | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_B))))),
% 2.07/2.26      inference('split', [status(esa)], ['79'])).
% 2.07/2.26  thf('116', plain,
% 2.07/2.26      ((![X36 : $i]:
% 2.07/2.26          (((X36) != (sk_D)) | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_C_1))))),
% 2.07/2.26      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 2.07/2.26  thf('117', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('simpl_trail', [status(thm)], ['81', '116'])).
% 2.07/2.26  thf('118', plain,
% 2.07/2.26      (((r1_tsep_1 @ sk_B @ sk_C_1)
% 2.07/2.26        | (v2_struct_0 @ sk_B)
% 2.07/2.26        | (v2_struct_0 @ sk_A)
% 2.07/2.26        | (v2_struct_0 @ sk_C_1))),
% 2.07/2.26      inference('sup-', [status(thm)], ['78', '117'])).
% 2.07/2.26  thf('119', plain, (~ (r1_tsep_1 @ sk_B @ sk_C_1)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('120', plain,
% 2.07/2.26      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 2.07/2.26      inference('sup-', [status(thm)], ['118', '119'])).
% 2.07/2.26  thf('121', plain, (~ (v2_struct_0 @ sk_C_1)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('122', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 2.07/2.26      inference('clc', [status(thm)], ['120', '121'])).
% 2.07/2.26  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 2.07/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.07/2.26  thf('124', plain, ((v2_struct_0 @ sk_A)),
% 2.07/2.26      inference('clc', [status(thm)], ['122', '123'])).
% 2.07/2.26  thf('125', plain, ($false), inference('demod', [status(thm)], ['0', '124'])).
% 2.07/2.26  
% 2.07/2.26  % SZS output end Refutation
% 2.07/2.26  
% 2.07/2.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
