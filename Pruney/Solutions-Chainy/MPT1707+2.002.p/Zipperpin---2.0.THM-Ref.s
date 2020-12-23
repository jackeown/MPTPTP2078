%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kaJvJ1FIzy

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:11 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 244 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :   29
%              Number of atoms          : 1478 (4984 expanded)
%              Number of equality atoms :   21 ( 181 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X26 @ X25 @ X27 ) @ X26 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X19 @ ( k1_connsp_2 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('20',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
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

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( v1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( X23
       != ( k1_tsep_1 @ X22 @ X21 @ X24 ) )
      | ( ( u1_struct_0 @ X23 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X22 @ X21 @ X24 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X22 @ X21 @ X24 ) @ X22 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X22 @ X21 @ X24 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X22 @ X21 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
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
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
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
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('43',plain,
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
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('54',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['62'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
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
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
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
    inference('sup-',[status(thm)],['23','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('71',plain,
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X28: $i] :
      ( ( X28 != sk_D_1 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X29: $i] :
      ( ( X29 != sk_D_1 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kaJvJ1FIzy
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:09:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.90/2.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.90/2.10  % Solved by: fo/fo7.sh
% 1.90/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.90/2.10  % done 1185 iterations in 1.643s
% 1.90/2.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.90/2.10  % SZS output start Refutation
% 1.90/2.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.90/2.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.90/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.90/2.10  thf(sk_C_type, type, sk_C: $i).
% 1.90/2.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.90/2.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.90/2.10  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.90/2.10  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.90/2.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.90/2.10  thf(sk_B_type, type, sk_B: $i).
% 1.90/2.10  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.90/2.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.90/2.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.90/2.10  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 1.90/2.10  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.90/2.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.90/2.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.90/2.10  thf(t16_tmap_1, conjecture,
% 1.90/2.10    (![A:$i]:
% 1.90/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.10       ( ![B:$i]:
% 1.90/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.90/2.10           ( ![C:$i]:
% 1.90/2.10             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.90/2.10               ( ![D:$i]:
% 1.90/2.10                 ( ( m1_subset_1 @
% 1.90/2.10                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.90/2.10                   ( ~( ( ![E:$i]:
% 1.90/2.10                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.90/2.10                            ( ( E ) != ( D ) ) ) ) & 
% 1.90/2.10                        ( ![E:$i]:
% 1.90/2.10                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.90/2.10                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.90/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.90/2.10    (~( ![A:$i]:
% 1.90/2.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.90/2.10            ( l1_pre_topc @ A ) ) =>
% 1.90/2.10          ( ![B:$i]:
% 1.90/2.10            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.90/2.10              ( ![C:$i]:
% 1.90/2.10                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.90/2.10                  ( ![D:$i]:
% 1.90/2.10                    ( ( m1_subset_1 @
% 1.90/2.10                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.90/2.10                      ( ~( ( ![E:$i]:
% 1.90/2.10                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.90/2.10                               ( ( E ) != ( D ) ) ) ) & 
% 1.90/2.10                           ( ![E:$i]:
% 1.90/2.10                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.90/2.10                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.90/2.10    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 1.90/2.10  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf(dt_k1_tsep_1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.90/2.10         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.90/2.10         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.90/2.10       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.90/2.10         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.90/2.10         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.90/2.10  thf('3', plain,
% 1.90/2.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.90/2.10         (~ (m1_pre_topc @ X25 @ X26)
% 1.90/2.10          | (v2_struct_0 @ X25)
% 1.90/2.10          | ~ (l1_pre_topc @ X26)
% 1.90/2.10          | (v2_struct_0 @ X26)
% 1.90/2.10          | (v2_struct_0 @ X27)
% 1.90/2.10          | ~ (m1_pre_topc @ X27 @ X26)
% 1.90/2.10          | (m1_pre_topc @ (k1_tsep_1 @ X26 @ X25 @ X27) @ X26))),
% 1.90/2.10      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.90/2.10  thf('4', plain,
% 1.90/2.10      (![X0 : $i]:
% 1.90/2.10         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.90/2.10          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.90/2.10          | (v2_struct_0 @ X0)
% 1.90/2.10          | (v2_struct_0 @ sk_A)
% 1.90/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.90/2.10          | (v2_struct_0 @ sk_B))),
% 1.90/2.10      inference('sup-', [status(thm)], ['2', '3'])).
% 1.90/2.10  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf('6', plain,
% 1.90/2.10      (![X0 : $i]:
% 1.90/2.10         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.90/2.10          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.90/2.10          | (v2_struct_0 @ X0)
% 1.90/2.10          | (v2_struct_0 @ sk_A)
% 1.90/2.10          | (v2_struct_0 @ sk_B))),
% 1.90/2.10      inference('demod', [status(thm)], ['4', '5'])).
% 1.90/2.10  thf('7', plain,
% 1.90/2.10      (((v2_struct_0 @ sk_B)
% 1.90/2.10        | (v2_struct_0 @ sk_A)
% 1.90/2.10        | (v2_struct_0 @ sk_C)
% 1.90/2.10        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.90/2.10      inference('sup-', [status(thm)], ['1', '6'])).
% 1.90/2.10  thf(dt_m1_pre_topc, axiom,
% 1.90/2.10    (![A:$i]:
% 1.90/2.10     ( ( l1_pre_topc @ A ) =>
% 1.90/2.10       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.90/2.10  thf('8', plain,
% 1.90/2.10      (![X15 : $i, X16 : $i]:
% 1.90/2.10         (~ (m1_pre_topc @ X15 @ X16)
% 1.90/2.10          | (l1_pre_topc @ X15)
% 1.90/2.10          | ~ (l1_pre_topc @ X16))),
% 1.90/2.10      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.90/2.10  thf('9', plain,
% 1.90/2.10      (((v2_struct_0 @ sk_C)
% 1.90/2.10        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['7', '8'])).
% 1.90/2.11  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('11', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('demod', [status(thm)], ['9', '10'])).
% 1.90/2.11  thf('12', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['1', '6'])).
% 1.90/2.11  thf(cc1_pre_topc, axiom,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.90/2.11  thf('13', plain,
% 1.90/2.11      (![X13 : $i, X14 : $i]:
% 1.90/2.11         (~ (m1_pre_topc @ X13 @ X14)
% 1.90/2.11          | (v2_pre_topc @ X13)
% 1.90/2.11          | ~ (l1_pre_topc @ X14)
% 1.90/2.11          | ~ (v2_pre_topc @ X14))),
% 1.90/2.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.90/2.11  thf('14', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ~ (v2_pre_topc @ sk_A)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['12', '13'])).
% 1.90/2.11  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('17', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.90/2.11  thf('18', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(t30_connsp_2, axiom,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.11       ( ![B:$i]:
% 1.90/2.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.90/2.11           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 1.90/2.11  thf('19', plain,
% 1.90/2.11      (![X19 : $i, X20 : $i]:
% 1.90/2.11         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.90/2.11          | (r2_hidden @ X19 @ (k1_connsp_2 @ X20 @ X19))
% 1.90/2.11          | ~ (l1_pre_topc @ X20)
% 1.90/2.11          | ~ (v2_pre_topc @ X20)
% 1.90/2.11          | (v2_struct_0 @ X20))),
% 1.90/2.11      inference('cnf', [status(esa)], [t30_connsp_2])).
% 1.90/2.11  thf('20', plain,
% 1.90/2.11      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ 
% 1.90/2.11           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['18', '19'])).
% 1.90/2.11  thf('21', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ 
% 1.90/2.11           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.90/2.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['17', '20'])).
% 1.90/2.11  thf('22', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ 
% 1.90/2.11           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['11', '21'])).
% 1.90/2.11  thf('23', plain,
% 1.90/2.11      (((r2_hidden @ sk_D_1 @ 
% 1.90/2.11         (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['22'])).
% 1.90/2.11  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('26', plain,
% 1.90/2.11      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.90/2.11         (~ (m1_pre_topc @ X25 @ X26)
% 1.90/2.11          | (v2_struct_0 @ X25)
% 1.90/2.11          | ~ (l1_pre_topc @ X26)
% 1.90/2.11          | (v2_struct_0 @ X26)
% 1.90/2.11          | (v2_struct_0 @ X27)
% 1.90/2.11          | ~ (m1_pre_topc @ X27 @ X26)
% 1.90/2.11          | (v1_pre_topc @ (k1_tsep_1 @ X26 @ X25 @ X27)))),
% 1.90/2.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.90/2.11  thf('27', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.90/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ X0)
% 1.90/2.11          | (v2_struct_0 @ sk_A)
% 1.90/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['25', '26'])).
% 1.90/2.11  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('29', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.90/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ X0)
% 1.90/2.11          | (v2_struct_0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('demod', [status(thm)], ['27', '28'])).
% 1.90/2.11  thf('30', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['24', '29'])).
% 1.90/2.11  thf('31', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['1', '6'])).
% 1.90/2.11  thf(d2_tsep_1, axiom,
% 1.90/2.11    (![A:$i]:
% 1.90/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.90/2.11       ( ![B:$i]:
% 1.90/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.90/2.11           ( ![C:$i]:
% 1.90/2.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.90/2.11               ( ![D:$i]:
% 1.90/2.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.90/2.11                     ( m1_pre_topc @ D @ A ) ) =>
% 1.90/2.11                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.90/2.11                     ( ( u1_struct_0 @ D ) =
% 1.90/2.11                       ( k2_xboole_0 @
% 1.90/2.11                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.90/2.11  thf('32', plain,
% 1.90/2.11      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.90/2.11         ((v2_struct_0 @ X21)
% 1.90/2.11          | ~ (m1_pre_topc @ X21 @ X22)
% 1.90/2.11          | (v2_struct_0 @ X23)
% 1.90/2.11          | ~ (v1_pre_topc @ X23)
% 1.90/2.11          | ~ (m1_pre_topc @ X23 @ X22)
% 1.90/2.11          | ((X23) != (k1_tsep_1 @ X22 @ X21 @ X24))
% 1.90/2.11          | ((u1_struct_0 @ X23)
% 1.90/2.11              = (k2_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24)))
% 1.90/2.11          | ~ (m1_pre_topc @ X24 @ X22)
% 1.90/2.11          | (v2_struct_0 @ X24)
% 1.90/2.11          | ~ (l1_pre_topc @ X22)
% 1.90/2.11          | (v2_struct_0 @ X22))),
% 1.90/2.11      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.90/2.11  thf('33', plain,
% 1.90/2.11      (![X21 : $i, X22 : $i, X24 : $i]:
% 1.90/2.11         ((v2_struct_0 @ X22)
% 1.90/2.11          | ~ (l1_pre_topc @ X22)
% 1.90/2.11          | (v2_struct_0 @ X24)
% 1.90/2.11          | ~ (m1_pre_topc @ X24 @ X22)
% 1.90/2.11          | ((u1_struct_0 @ (k1_tsep_1 @ X22 @ X21 @ X24))
% 1.90/2.11              = (k2_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24)))
% 1.90/2.11          | ~ (m1_pre_topc @ (k1_tsep_1 @ X22 @ X21 @ X24) @ X22)
% 1.90/2.11          | ~ (v1_pre_topc @ (k1_tsep_1 @ X22 @ X21 @ X24))
% 1.90/2.11          | (v2_struct_0 @ (k1_tsep_1 @ X22 @ X21 @ X24))
% 1.90/2.11          | ~ (m1_pre_topc @ X21 @ X22)
% 1.90/2.11          | (v2_struct_0 @ X21))),
% 1.90/2.11      inference('simplify', [status(thm)], ['32'])).
% 1.90/2.11  thf('34', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['31', '33'])).
% 1.90/2.11  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('38', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A))),
% 1.90/2.11      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.90/2.11  thf('39', plain,
% 1.90/2.11      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C))),
% 1.90/2.11      inference('simplify', [status(thm)], ['38'])).
% 1.90/2.11  thf('40', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['30', '39'])).
% 1.90/2.11  thf('41', plain,
% 1.90/2.11      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C))),
% 1.90/2.11      inference('simplify', [status(thm)], ['40'])).
% 1.90/2.11  thf('42', plain,
% 1.90/2.11      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.90/2.11         (~ (m1_pre_topc @ X25 @ X26)
% 1.90/2.11          | (v2_struct_0 @ X25)
% 1.90/2.11          | ~ (l1_pre_topc @ X26)
% 1.90/2.11          | (v2_struct_0 @ X26)
% 1.90/2.11          | (v2_struct_0 @ X27)
% 1.90/2.11          | ~ (m1_pre_topc @ X27 @ X26)
% 1.90/2.11          | ~ (v2_struct_0 @ (k1_tsep_1 @ X26 @ X25 @ X27)))),
% 1.90/2.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.90/2.11  thf('43', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['41', '42'])).
% 1.90/2.11  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('47', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 1.90/2.11  thf('48', plain,
% 1.90/2.11      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C))),
% 1.90/2.11      inference('simplify', [status(thm)], ['47'])).
% 1.90/2.11  thf('49', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(t2_subset, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( m1_subset_1 @ A @ B ) =>
% 1.90/2.11       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.90/2.11  thf('50', plain,
% 1.90/2.11      (![X8 : $i, X9 : $i]:
% 1.90/2.11         ((r2_hidden @ X8 @ X9)
% 1.90/2.11          | (v1_xboole_0 @ X9)
% 1.90/2.11          | ~ (m1_subset_1 @ X8 @ X9))),
% 1.90/2.11      inference('cnf', [status(esa)], [t2_subset])).
% 1.90/2.11  thf('51', plain,
% 1.90/2.11      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ 
% 1.90/2.11           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['49', '50'])).
% 1.90/2.11  thf('52', plain,
% 1.90/2.11      (((r2_hidden @ sk_D_1 @ 
% 1.90/2.11         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.11      inference('sup+', [status(thm)], ['48', '51'])).
% 1.90/2.11  thf(d3_xboole_0, axiom,
% 1.90/2.11    (![A:$i,B:$i,C:$i]:
% 1.90/2.11     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.90/2.11       ( ![D:$i]:
% 1.90/2.11         ( ( r2_hidden @ D @ C ) <=>
% 1.90/2.11           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.90/2.11  thf('53', plain,
% 1.90/2.11      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X4 @ X2)
% 1.90/2.11          | (r2_hidden @ X4 @ X3)
% 1.90/2.11          | (r2_hidden @ X4 @ X1)
% 1.90/2.11          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.90/2.11      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.90/2.11  thf('54', plain,
% 1.90/2.11      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.90/2.11         ((r2_hidden @ X4 @ X1)
% 1.90/2.11          | (r2_hidden @ X4 @ X3)
% 1.90/2.11          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['53'])).
% 1.90/2.11  thf('55', plain,
% 1.90/2.11      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['52', '54'])).
% 1.90/2.11  thf('56', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('demod', [status(thm)], ['9', '10'])).
% 1.90/2.11  thf('57', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.90/2.11  thf('58', plain,
% 1.90/2.11      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf(dt_k1_connsp_2, axiom,
% 1.90/2.11    (![A:$i,B:$i]:
% 1.90/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.90/2.11         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.90/2.11       ( m1_subset_1 @
% 1.90/2.11         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.90/2.11  thf('59', plain,
% 1.90/2.11      (![X17 : $i, X18 : $i]:
% 1.90/2.11         (~ (l1_pre_topc @ X17)
% 1.90/2.11          | ~ (v2_pre_topc @ X17)
% 1.90/2.11          | (v2_struct_0 @ X17)
% 1.90/2.11          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.90/2.11          | (m1_subset_1 @ (k1_connsp_2 @ X17 @ X18) @ 
% 1.90/2.11             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 1.90/2.11      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 1.90/2.11  thf('60', plain,
% 1.90/2.11      (((m1_subset_1 @ 
% 1.90/2.11         (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.90/2.11         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['58', '59'])).
% 1.90/2.11  thf('61', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (m1_subset_1 @ 
% 1.90/2.11           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.90/2.11           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))))),
% 1.90/2.11      inference('sup-', [status(thm)], ['57', '60'])).
% 1.90/2.11  thf('62', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (m1_subset_1 @ 
% 1.90/2.11           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.90/2.11           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['56', '61'])).
% 1.90/2.11  thf('63', plain,
% 1.90/2.11      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (m1_subset_1 @ 
% 1.90/2.11           (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1) @ 
% 1.90/2.11           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['62'])).
% 1.90/2.11  thf(t5_subset, axiom,
% 1.90/2.11    (![A:$i,B:$i,C:$i]:
% 1.90/2.11     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.90/2.11          ( v1_xboole_0 @ C ) ) ))).
% 1.90/2.11  thf('64', plain,
% 1.90/2.11      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.90/2.11         (~ (r2_hidden @ X10 @ X11)
% 1.90/2.11          | ~ (v1_xboole_0 @ X12)
% 1.90/2.11          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.90/2.11      inference('cnf', [status(esa)], [t5_subset])).
% 1.90/2.11  thf('65', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((v2_struct_0 @ sk_B)
% 1.90/2.11          | (v2_struct_0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ sk_C)
% 1.90/2.11          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11          | ~ (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.90/2.11          | ~ (r2_hidden @ X0 @ 
% 1.90/2.11               (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['63', '64'])).
% 1.90/2.11  thf('66', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11          | (v2_struct_0 @ sk_C)
% 1.90/2.11          | (v2_struct_0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ sk_B)
% 1.90/2.11          | ~ (r2_hidden @ X0 @ 
% 1.90/2.11               (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.90/2.11          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11          | (v2_struct_0 @ sk_C)
% 1.90/2.11          | (v2_struct_0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['55', '65'])).
% 1.90/2.11  thf('67', plain,
% 1.90/2.11      (![X0 : $i]:
% 1.90/2.11         ((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11          | ~ (r2_hidden @ X0 @ 
% 1.90/2.11               (k1_connsp_2 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 1.90/2.11          | (v2_struct_0 @ sk_B)
% 1.90/2.11          | (v2_struct_0 @ sk_A)
% 1.90/2.11          | (v2_struct_0 @ sk_C)
% 1.90/2.11          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.90/2.11      inference('simplify', [status(thm)], ['66'])).
% 1.90/2.11  thf('68', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['23', '67'])).
% 1.90/2.11  thf('69', plain,
% 1.90/2.11      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['68'])).
% 1.90/2.11  thf('70', plain,
% 1.90/2.11      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.90/2.11         (~ (m1_pre_topc @ X25 @ X26)
% 1.90/2.11          | (v2_struct_0 @ X25)
% 1.90/2.11          | ~ (l1_pre_topc @ X26)
% 1.90/2.11          | (v2_struct_0 @ X26)
% 1.90/2.11          | (v2_struct_0 @ X27)
% 1.90/2.11          | ~ (m1_pre_topc @ X27 @ X26)
% 1.90/2.11          | ~ (v2_struct_0 @ (k1_tsep_1 @ X26 @ X25 @ X27)))),
% 1.90/2.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.90/2.11  thf('71', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.90/2.11      inference('sup-', [status(thm)], ['69', '70'])).
% 1.90/2.11  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('75', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 1.90/2.11  thf('76', plain,
% 1.90/2.11      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['75'])).
% 1.90/2.11  thf(t1_subset, axiom,
% 1.90/2.11    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.90/2.11  thf('77', plain,
% 1.90/2.11      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.90/2.11      inference('cnf', [status(esa)], [t1_subset])).
% 1.90/2.11  thf('78', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['76', '77'])).
% 1.90/2.11  thf('79', plain,
% 1.90/2.11      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.90/2.11      inference('cnf', [status(esa)], [t1_subset])).
% 1.90/2.11  thf('80', plain,
% 1.90/2.11      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.90/2.11        | (v2_struct_0 @ sk_C)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 1.90/2.11      inference('sup-', [status(thm)], ['78', '79'])).
% 1.90/2.11  thf('81', plain,
% 1.90/2.11      (![X28 : $i]:
% 1.90/2.11         (((X28) != (sk_D_1)) | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_C)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('82', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 1.90/2.11      inference('simplify', [status(thm)], ['81'])).
% 1.90/2.11  thf('83', plain,
% 1.90/2.11      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.90/2.11        | (v2_struct_0 @ sk_B)
% 1.90/2.11        | (v2_struct_0 @ sk_A)
% 1.90/2.11        | (v2_struct_0 @ sk_C))),
% 1.90/2.11      inference('sup-', [status(thm)], ['80', '82'])).
% 1.90/2.11  thf('84', plain,
% 1.90/2.11      (![X29 : $i]:
% 1.90/2.11         (((X29) != (sk_D_1)) | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_B)))),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('85', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 1.90/2.11      inference('simplify', [status(thm)], ['84'])).
% 1.90/2.11  thf('86', plain,
% 1.90/2.11      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 1.90/2.11      inference('sup-', [status(thm)], ['83', '85'])).
% 1.90/2.11  thf('87', plain, (~ (v2_struct_0 @ sk_C)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('88', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 1.90/2.11      inference('clc', [status(thm)], ['86', '87'])).
% 1.90/2.11  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 1.90/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.11  thf('90', plain, ((v2_struct_0 @ sk_A)),
% 1.90/2.11      inference('clc', [status(thm)], ['88', '89'])).
% 1.90/2.11  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 1.90/2.11  
% 1.90/2.11  % SZS output end Refutation
% 1.90/2.11  
% 1.90/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
