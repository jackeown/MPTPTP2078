%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y6nEPgrg59

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:12 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 230 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   29
%              Number of atoms          : 1523 (4746 expanded)
%              Number of equality atoms :   21 ( 173 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t16_tmap_1,conjecture,(
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
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ~ ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                         => ( E != D ) )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                         => ( E != D ) ) ) ) ) ) ) )).

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
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                   => ~ ( ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                           => ( E != D ) )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                           => ( E != D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v2_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_pre_topc @ ( k1_tsep_1 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tmap_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X17 @ ( k1_connsp_2 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('22',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( X21
       != ( k1_tsep_1 @ X20 @ X19 @ X22 ) )
      | ( ( u1_struct_0 @ X21 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('35',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X20 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('56',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('60',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['77'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X29: $i] :
      ( ( X29 != sk_D_1 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X30: $i] :
      ( ( X30 != sk_D_1 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y6nEPgrg59
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.72/1.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.93  % Solved by: fo/fo7.sh
% 1.72/1.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.93  % done 974 iterations in 1.481s
% 1.72/1.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.93  % SZS output start Refutation
% 1.72/1.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.93  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.72/1.93  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.72/1.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.72/1.93  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.72/1.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.72/1.93  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.93  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.93  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.93  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 1.72/1.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.72/1.93  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.72/1.93  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.72/1.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.72/1.93  thf(t16_tmap_1, conjecture,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.72/1.93           ( ![C:$i]:
% 1.72/1.93             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.72/1.93               ( ![D:$i]:
% 1.72/1.93                 ( ( m1_subset_1 @
% 1.72/1.93                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.72/1.93                   ( ~( ( ![E:$i]:
% 1.72/1.93                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.72/1.93                            ( ( E ) != ( D ) ) ) ) & 
% 1.72/1.93                        ( ![E:$i]:
% 1.72/1.93                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.72/1.93                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.72/1.93  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.93    (~( ![A:$i]:
% 1.72/1.93        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.72/1.93            ( l1_pre_topc @ A ) ) =>
% 1.72/1.93          ( ![B:$i]:
% 1.72/1.93            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.72/1.93              ( ![C:$i]:
% 1.72/1.93                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.72/1.93                  ( ![D:$i]:
% 1.72/1.93                    ( ( m1_subset_1 @
% 1.72/1.93                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.72/1.93                      ( ~( ( ![E:$i]:
% 1.72/1.93                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.72/1.93                               ( ( E ) != ( D ) ) ) ) & 
% 1.72/1.93                           ( ![E:$i]:
% 1.72/1.93                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.72/1.93                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.72/1.93    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 1.72/1.93  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(dt_k1_tsep_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.72/1.93         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.72/1.93         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.72/1.93       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.72/1.93         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.72/1.93         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.72/1.93  thf('3', plain,
% 1.72/1.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.93         (~ (m1_pre_topc @ X23 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X23)
% 1.72/1.93          | ~ (l1_pre_topc @ X24)
% 1.72/1.93          | (v2_struct_0 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X25)
% 1.72/1.93          | ~ (m1_pre_topc @ X25 @ X24)
% 1.72/1.93          | (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X25) @ X24))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.72/1.93  thf('4', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.72/1.93          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ X0)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('sup-', [status(thm)], ['2', '3'])).
% 1.72/1.93  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('6', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.72/1.93          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ X0)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['4', '5'])).
% 1.72/1.93  thf('7', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['1', '6'])).
% 1.72/1.93  thf(dt_m1_pre_topc, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( l1_pre_topc @ A ) =>
% 1.72/1.93       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.72/1.93  thf('8', plain,
% 1.72/1.93      (![X13 : $i, X14 : $i]:
% 1.72/1.93         (~ (m1_pre_topc @ X13 @ X14)
% 1.72/1.93          | (l1_pre_topc @ X13)
% 1.72/1.93          | ~ (l1_pre_topc @ X14))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.72/1.93  thf('9', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['7', '8'])).
% 1.72/1.93  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('11', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.72/1.93  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(fc1_tmap_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.72/1.93         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.72/1.93         ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ C ) ) & 
% 1.72/1.93         ( m1_pre_topc @ C @ A ) ) =>
% 1.72/1.93       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.72/1.93         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.72/1.93         ( v2_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) ) ))).
% 1.72/1.93  thf('14', plain,
% 1.72/1.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.72/1.93         (~ (m1_pre_topc @ X26 @ X27)
% 1.72/1.93          | (v2_struct_0 @ X26)
% 1.72/1.93          | ~ (l1_pre_topc @ X27)
% 1.72/1.93          | ~ (v2_pre_topc @ X27)
% 1.72/1.93          | (v2_struct_0 @ X27)
% 1.72/1.93          | (v2_struct_0 @ X28)
% 1.72/1.93          | ~ (m1_pre_topc @ X28 @ X27)
% 1.72/1.93          | (v2_pre_topc @ (k1_tsep_1 @ X27 @ X26 @ X28)))),
% 1.72/1.93      inference('cnf', [status(esa)], [fc1_tmap_1])).
% 1.72/1.93  thf('15', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.72/1.93          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ X0)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | ~ (v2_pre_topc @ sk_A)
% 1.72/1.93          | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.93  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('18', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.72/1.93          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ X0)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.72/1.93  thf('19', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['12', '18'])).
% 1.72/1.93  thf('20', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t30_connsp_2, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.72/1.93           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 1.72/1.93  thf('21', plain,
% 1.72/1.93      (![X17 : $i, X18 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 1.72/1.93          | (r2_hidden @ X17 @ (k1_connsp_2 @ X18 @ X17))
% 1.72/1.93          | ~ (l1_pre_topc @ X18)
% 1.72/1.93          | ~ (v2_pre_topc @ X18)
% 1.72/1.93          | (v2_struct_0 @ X18))),
% 1.72/1.93      inference('cnf', [status(esa)], [t30_connsp_2])).
% 1.72/1.93  thf('22', plain,
% 1.72/1.93      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ 
% 1.72/1.93           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['20', '21'])).
% 1.72/1.93  thf('23', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ 
% 1.72/1.93           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.72/1.93        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['19', '22'])).
% 1.72/1.93  thf('24', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ 
% 1.72/1.93           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['11', '23'])).
% 1.72/1.93  thf('25', plain,
% 1.72/1.93      (((r2_hidden @ sk_D_1 @ 
% 1.72/1.93         (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('simplify', [status(thm)], ['24'])).
% 1.72/1.93  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('28', plain,
% 1.72/1.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.93         (~ (m1_pre_topc @ X23 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X23)
% 1.72/1.93          | ~ (l1_pre_topc @ X24)
% 1.72/1.93          | (v2_struct_0 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X25)
% 1.72/1.93          | ~ (m1_pre_topc @ X25 @ X24)
% 1.72/1.93          | (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X25)))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.72/1.93  thf('29', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.72/1.93          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ X0)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.93  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('31', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.72/1.93          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ X0)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['29', '30'])).
% 1.72/1.93  thf('32', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['26', '31'])).
% 1.72/1.93  thf('33', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['1', '6'])).
% 1.72/1.93  thf(d2_tsep_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.72/1.93           ( ![C:$i]:
% 1.72/1.93             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.72/1.93               ( ![D:$i]:
% 1.72/1.93                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.72/1.93                     ( m1_pre_topc @ D @ A ) ) =>
% 1.72/1.93                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.72/1.93                     ( ( u1_struct_0 @ D ) =
% 1.72/1.93                       ( k2_xboole_0 @
% 1.72/1.93                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.72/1.93  thf('34', plain,
% 1.72/1.93      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.72/1.93         ((v2_struct_0 @ X19)
% 1.72/1.93          | ~ (m1_pre_topc @ X19 @ X20)
% 1.72/1.93          | (v2_struct_0 @ X21)
% 1.72/1.93          | ~ (v1_pre_topc @ X21)
% 1.72/1.93          | ~ (m1_pre_topc @ X21 @ X20)
% 1.72/1.93          | ((X21) != (k1_tsep_1 @ X20 @ X19 @ X22))
% 1.72/1.93          | ((u1_struct_0 @ X21)
% 1.72/1.93              = (k2_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22)))
% 1.72/1.93          | ~ (m1_pre_topc @ X22 @ X20)
% 1.72/1.93          | (v2_struct_0 @ X22)
% 1.72/1.93          | ~ (l1_pre_topc @ X20)
% 1.72/1.93          | (v2_struct_0 @ X20))),
% 1.72/1.93      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.72/1.93  thf('35', plain,
% 1.72/1.93      (![X19 : $i, X20 : $i, X22 : $i]:
% 1.72/1.93         ((v2_struct_0 @ X20)
% 1.72/1.93          | ~ (l1_pre_topc @ X20)
% 1.72/1.93          | (v2_struct_0 @ X22)
% 1.72/1.93          | ~ (m1_pre_topc @ X22 @ X20)
% 1.72/1.93          | ((u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22))
% 1.72/1.93              = (k2_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22)))
% 1.72/1.93          | ~ (m1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X20)
% 1.72/1.93          | ~ (v1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X22))
% 1.72/1.93          | (v2_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22))
% 1.72/1.93          | ~ (m1_pre_topc @ X19 @ X20)
% 1.72/1.93          | (v2_struct_0 @ X19))),
% 1.72/1.93      inference('simplify', [status(thm)], ['34'])).
% 1.72/1.93  thf('36', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['33', '35'])).
% 1.72/1.93  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('40', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 1.72/1.93  thf('41', plain,
% 1.72/1.93      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C))),
% 1.72/1.93      inference('simplify', [status(thm)], ['40'])).
% 1.72/1.93  thf('42', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['32', '41'])).
% 1.72/1.93  thf('43', plain,
% 1.72/1.93      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C))),
% 1.72/1.93      inference('simplify', [status(thm)], ['42'])).
% 1.72/1.93  thf('44', plain,
% 1.72/1.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.93         (~ (m1_pre_topc @ X23 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X23)
% 1.72/1.93          | ~ (l1_pre_topc @ X24)
% 1.72/1.93          | (v2_struct_0 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X25)
% 1.72/1.93          | ~ (m1_pre_topc @ X25 @ X24)
% 1.72/1.93          | ~ (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X25)))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.72/1.93  thf('45', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['43', '44'])).
% 1.72/1.93  thf('46', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('48', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('49', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 1.72/1.93  thf('50', plain,
% 1.72/1.93      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C))),
% 1.72/1.93      inference('simplify', [status(thm)], ['49'])).
% 1.72/1.93  thf('51', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t2_subset, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( m1_subset_1 @ A @ B ) =>
% 1.72/1.93       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.72/1.93  thf('52', plain,
% 1.72/1.93      (![X8 : $i, X9 : $i]:
% 1.72/1.93         ((r2_hidden @ X8 @ X9)
% 1.72/1.93          | (v1_xboole_0 @ X9)
% 1.72/1.93          | ~ (m1_subset_1 @ X8 @ X9))),
% 1.72/1.93      inference('cnf', [status(esa)], [t2_subset])).
% 1.72/1.93  thf('53', plain,
% 1.72/1.93      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ 
% 1.72/1.93           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['51', '52'])).
% 1.72/1.93  thf('54', plain,
% 1.72/1.93      (((r2_hidden @ sk_D_1 @ 
% 1.72/1.93         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['50', '53'])).
% 1.72/1.93  thf(d3_xboole_0, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.72/1.93       ( ![D:$i]:
% 1.72/1.93         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.93           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.72/1.93  thf('55', plain,
% 1.72/1.93      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X4 @ X2)
% 1.72/1.93          | (r2_hidden @ X4 @ X3)
% 1.72/1.93          | (r2_hidden @ X4 @ X1)
% 1.72/1.93          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.72/1.93      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.72/1.93  thf('56', plain,
% 1.72/1.93      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.72/1.93         ((r2_hidden @ X4 @ X1)
% 1.72/1.93          | (r2_hidden @ X4 @ X3)
% 1.72/1.93          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['55'])).
% 1.72/1.93  thf('57', plain,
% 1.72/1.93      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['54', '56'])).
% 1.72/1.93  thf('58', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.72/1.93  thf('59', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['12', '18'])).
% 1.72/1.93  thf('60', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(dt_k1_connsp_2, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.72/1.93         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.93       ( m1_subset_1 @
% 1.72/1.93         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.72/1.93  thf('61', plain,
% 1.72/1.93      (![X15 : $i, X16 : $i]:
% 1.72/1.93         (~ (l1_pre_topc @ X15)
% 1.72/1.93          | ~ (v2_pre_topc @ X15)
% 1.72/1.93          | (v2_struct_0 @ X15)
% 1.72/1.93          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 1.72/1.93          | (m1_subset_1 @ (k1_connsp_2 @ X15 @ X16) @ 
% 1.72/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 1.72/1.93  thf('62', plain,
% 1.72/1.93      (((m1_subset_1 @ 
% 1.72/1.93         (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.72/1.93         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['60', '61'])).
% 1.72/1.93  thf('63', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (m1_subset_1 @ 
% 1.72/1.93           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['59', '62'])).
% 1.72/1.93  thf('64', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (m1_subset_1 @ 
% 1.72/1.93           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['58', '63'])).
% 1.72/1.93  thf('65', plain,
% 1.72/1.93      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (m1_subset_1 @ 
% 1.72/1.93           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.72/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('simplify', [status(thm)], ['64'])).
% 1.72/1.93  thf(t5_subset, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.72/1.93          ( v1_xboole_0 @ C ) ) ))).
% 1.72/1.93  thf('66', plain,
% 1.72/1.93      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X10 @ X11)
% 1.72/1.93          | ~ (v1_xboole_0 @ X12)
% 1.72/1.93          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.72/1.93      inference('cnf', [status(esa)], [t5_subset])).
% 1.72/1.93  thf('67', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((v2_struct_0 @ sk_B)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_C)
% 1.72/1.93          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93          | ~ (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.72/1.93          | ~ (r2_hidden @ X0 @ 
% 1.72/1.93               (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['65', '66'])).
% 1.72/1.93  thf('68', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93          | (v2_struct_0 @ sk_C)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B)
% 1.72/1.93          | ~ (r2_hidden @ X0 @ 
% 1.72/1.93               (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.72/1.93          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93          | (v2_struct_0 @ sk_C)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('sup-', [status(thm)], ['57', '67'])).
% 1.72/1.93  thf('69', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93          | ~ (r2_hidden @ X0 @ 
% 1.72/1.93               (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.72/1.93          | (v2_struct_0 @ sk_B)
% 1.72/1.93          | (v2_struct_0 @ sk_A)
% 1.72/1.93          | (v2_struct_0 @ sk_C)
% 1.72/1.93          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['68'])).
% 1.72/1.93  thf('70', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['25', '69'])).
% 1.72/1.93  thf('71', plain,
% 1.72/1.93      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('simplify', [status(thm)], ['70'])).
% 1.72/1.93  thf('72', plain,
% 1.72/1.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.93         (~ (m1_pre_topc @ X23 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X23)
% 1.72/1.93          | ~ (l1_pre_topc @ X24)
% 1.72/1.93          | (v2_struct_0 @ X24)
% 1.72/1.93          | (v2_struct_0 @ X25)
% 1.72/1.93          | ~ (m1_pre_topc @ X25 @ X24)
% 1.72/1.93          | ~ (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X25)))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.72/1.93  thf('73', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | ~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['71', '72'])).
% 1.72/1.93  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('76', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('77', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 1.72/1.93  thf('78', plain,
% 1.72/1.93      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('simplify', [status(thm)], ['77'])).
% 1.72/1.93  thf(t1_subset, axiom,
% 1.72/1.93    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.72/1.93  thf('79', plain,
% 1.72/1.93      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.72/1.93      inference('cnf', [status(esa)], [t1_subset])).
% 1.72/1.93  thf('80', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['78', '79'])).
% 1.72/1.93  thf('81', plain,
% 1.72/1.93      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.72/1.93      inference('cnf', [status(esa)], [t1_subset])).
% 1.72/1.93  thf('82', plain,
% 1.72/1.93      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.72/1.93        | (v2_struct_0 @ sk_C)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['80', '81'])).
% 1.72/1.93  thf('83', plain,
% 1.72/1.93      (![X29 : $i]:
% 1.72/1.93         (((X29) != (sk_D_1)) | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_C)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('84', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 1.72/1.93      inference('simplify', [status(thm)], ['83'])).
% 1.72/1.93  thf('85', plain,
% 1.72/1.93      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.72/1.93        | (v2_struct_0 @ sk_B)
% 1.72/1.93        | (v2_struct_0 @ sk_A)
% 1.72/1.93        | (v2_struct_0 @ sk_C))),
% 1.72/1.93      inference('sup-', [status(thm)], ['82', '84'])).
% 1.72/1.93  thf('86', plain,
% 1.72/1.93      (![X30 : $i]:
% 1.72/1.93         (((X30) != (sk_D_1)) | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_B)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('87', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 1.72/1.93      inference('simplify', [status(thm)], ['86'])).
% 1.72/1.93  thf('88', plain,
% 1.72/1.93      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 1.72/1.93      inference('sup-', [status(thm)], ['85', '87'])).
% 1.72/1.93  thf('89', plain, (~ (v2_struct_0 @ sk_C)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('90', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 1.72/1.93      inference('clc', [status(thm)], ['88', '89'])).
% 1.72/1.93  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('92', plain, ((v2_struct_0 @ sk_A)),
% 1.72/1.93      inference('clc', [status(thm)], ['90', '91'])).
% 1.72/1.93  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 1.72/1.93  
% 1.72/1.93  % SZS output end Refutation
% 1.72/1.93  
% 1.72/1.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
