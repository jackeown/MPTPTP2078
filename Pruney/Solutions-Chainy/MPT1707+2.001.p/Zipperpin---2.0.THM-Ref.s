%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bPEPWqR9cv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:11 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 240 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :   31
%              Number of atoms          : 1118 (4724 expanded)
%              Number of equality atoms :   22 ( 190 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_pre_topc @ sk_B_1 @ sk_A ),
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
      | ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

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

thf('15',plain,(
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

thf('16',plain,(
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
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(fc4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_xboole_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X26: $i] :
      ( ( X26 != sk_D_1 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X27: $i] :
      ( ( X27 != sk_D_1 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','62','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('74',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['60','61'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bPEPWqR9cv
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 390 iterations in 0.353s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.61/0.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.84  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.61/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.61/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.84  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.84  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.61/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.84  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.61/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.84  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.84  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.61/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.84  thf(t16_tmap_1, conjecture,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.61/0.84               ( ![D:$i]:
% 0.61/0.84                 ( ( m1_subset_1 @
% 0.61/0.84                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.61/0.84                   ( ~( ( ![E:$i]:
% 0.61/0.84                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.61/0.84                            ( ( E ) != ( D ) ) ) ) & 
% 0.61/0.84                        ( ![E:$i]:
% 0.61/0.84                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.61/0.84                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i]:
% 0.61/0.84        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.61/0.84            ( l1_pre_topc @ A ) ) =>
% 0.61/0.84          ( ![B:$i]:
% 0.61/0.84            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.61/0.84              ( ![C:$i]:
% 0.61/0.84                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.61/0.84                  ( ![D:$i]:
% 0.61/0.84                    ( ( m1_subset_1 @
% 0.61/0.84                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.61/0.84                      ( ~( ( ![E:$i]:
% 0.61/0.84                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.61/0.84                               ( ( E ) != ( D ) ) ) ) & 
% 0.61/0.84                           ( ![E:$i]:
% 0.61/0.84                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.61/0.84                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 0.61/0.84  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('2', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(dt_k1_tsep_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.61/0.84         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.61/0.84         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.61/0.84       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.61/0.84         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.61/0.84         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.61/0.84  thf('3', plain,
% 0.61/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.84         (~ (m1_pre_topc @ X23 @ X24)
% 0.61/0.84          | (v2_struct_0 @ X23)
% 0.61/0.84          | ~ (l1_pre_topc @ X24)
% 0.61/0.84          | (v2_struct_0 @ X24)
% 0.61/0.84          | (v2_struct_0 @ X25)
% 0.61/0.84          | ~ (m1_pre_topc @ X25 @ X24)
% 0.61/0.84          | (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X25)))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.61/0.84  thf('4', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0))
% 0.61/0.84          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ X0)
% 0.61/0.84          | (v2_struct_0 @ sk_A)
% 0.61/0.84          | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.84  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('6', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0))
% 0.61/0.84          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ X0)
% 0.61/0.84          | (v2_struct_0 @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.61/0.84  thf('7', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['1', '6'])).
% 0.61/0.84  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('9', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('10', plain,
% 0.61/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.84         (~ (m1_pre_topc @ X23 @ X24)
% 0.61/0.84          | (v2_struct_0 @ X23)
% 0.61/0.84          | ~ (l1_pre_topc @ X24)
% 0.61/0.84          | (v2_struct_0 @ X24)
% 0.61/0.84          | (v2_struct_0 @ X25)
% 0.61/0.84          | ~ (m1_pre_topc @ X25 @ X24)
% 0.61/0.84          | (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X25) @ X24))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.61/0.84  thf('11', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.61/0.84          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ X0)
% 0.61/0.84          | (v2_struct_0 @ sk_A)
% 0.61/0.84          | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.84  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.61/0.84          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ X0)
% 0.61/0.84          | (v2_struct_0 @ sk_A)
% 0.61/0.84          | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C) @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['8', '13'])).
% 0.61/0.84  thf(d2_tsep_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.61/0.84               ( ![D:$i]:
% 0.61/0.84                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.61/0.84                     ( m1_pre_topc @ D @ A ) ) =>
% 0.61/0.84                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.61/0.84                     ( ( u1_struct_0 @ D ) =
% 0.61/0.84                       ( k2_xboole_0 @
% 0.61/0.84                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.61/0.84         ((v2_struct_0 @ X19)
% 0.61/0.84          | ~ (m1_pre_topc @ X19 @ X20)
% 0.61/0.84          | (v2_struct_0 @ X21)
% 0.61/0.84          | ~ (v1_pre_topc @ X21)
% 0.61/0.84          | ~ (m1_pre_topc @ X21 @ X20)
% 0.61/0.84          | ((X21) != (k1_tsep_1 @ X20 @ X19 @ X22))
% 0.61/0.84          | ((u1_struct_0 @ X21)
% 0.61/0.84              = (k2_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22)))
% 0.61/0.84          | ~ (m1_pre_topc @ X22 @ X20)
% 0.61/0.84          | (v2_struct_0 @ X22)
% 0.61/0.84          | ~ (l1_pre_topc @ X20)
% 0.61/0.84          | (v2_struct_0 @ X20))),
% 0.61/0.84      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.61/0.84  thf('16', plain,
% 0.61/0.84      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.61/0.84         ((v2_struct_0 @ X20)
% 0.61/0.84          | ~ (l1_pre_topc @ X20)
% 0.61/0.84          | (v2_struct_0 @ X22)
% 0.61/0.84          | ~ (m1_pre_topc @ X22 @ X20)
% 0.61/0.84          | ((u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22))
% 0.61/0.84              = (k2_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22)))
% 0.61/0.84          | ~ (m1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X20)
% 0.61/0.84          | ~ (v1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X22))
% 0.61/0.84          | (v2_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22))
% 0.61/0.84          | ~ (m1_pre_topc @ X19 @ X20)
% 0.61/0.84          | (v2_struct_0 @ X19))),
% 0.61/0.84      inference('simplify', [status(thm)], ['15'])).
% 0.61/0.84  thf('17', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['14', '16'])).
% 0.61/0.84  thf('18', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C))),
% 0.61/0.84      inference('simplify', [status(thm)], ['21'])).
% 0.61/0.84  thf('23', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['7', '22'])).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C))),
% 0.61/0.84      inference('simplify', [status(thm)], ['23'])).
% 0.61/0.84  thf('25', plain,
% 0.61/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.84         (~ (m1_pre_topc @ X23 @ X24)
% 0.61/0.84          | (v2_struct_0 @ X23)
% 0.61/0.84          | ~ (l1_pre_topc @ X24)
% 0.61/0.84          | (v2_struct_0 @ X24)
% 0.61/0.84          | (v2_struct_0 @ X25)
% 0.61/0.84          | ~ (m1_pre_topc @ X25 @ X24)
% 0.61/0.84          | ~ (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X25)))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.84  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('29', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84            = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.61/0.84  thf('31', plain,
% 0.61/0.84      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C))),
% 0.61/0.84      inference('simplify', [status(thm)], ['30'])).
% 0.61/0.84  thf('32', plain,
% 0.61/0.84      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.61/0.84          = (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C))),
% 0.61/0.84      inference('simplify', [status(thm)], ['30'])).
% 0.61/0.84  thf('33', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_D_1 @ 
% 0.61/0.84        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t2_subset, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ A @ B ) =>
% 0.61/0.84       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.61/0.84  thf('34', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i]:
% 0.61/0.84         ((r2_hidden @ X12 @ X13)
% 0.61/0.84          | (v1_xboole_0 @ X13)
% 0.61/0.84          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.61/0.84      inference('cnf', [status(esa)], [t2_subset])).
% 0.61/0.84  thf('35', plain,
% 0.61/0.84      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ 
% 0.61/0.84           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.61/0.84  thf('36', plain,
% 0.61/0.84      (((r2_hidden @ sk_D_1 @ 
% 0.61/0.84         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C))))),
% 0.61/0.84      inference('sup+', [status(thm)], ['32', '35'])).
% 0.61/0.84  thf(d3_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.61/0.84       ( ![D:$i]:
% 0.61/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.84           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.61/0.84  thf('37', plain,
% 0.61/0.84      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X4 @ X2)
% 0.61/0.84          | (r2_hidden @ X4 @ X3)
% 0.61/0.84          | (r2_hidden @ X4 @ X1)
% 0.61/0.84          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.61/0.84  thf('38', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.61/0.84         ((r2_hidden @ X4 @ X1)
% 0.61/0.84          | (r2_hidden @ X4 @ X3)
% 0.61/0.84          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['37'])).
% 0.61/0.84  thf('39', plain,
% 0.61/0.84      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B_1 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['36', '38'])).
% 0.61/0.84  thf('40', plain,
% 0.61/0.84      (((v1_xboole_0 @ 
% 0.61/0.84         (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('sup+', [status(thm)], ['31', '39'])).
% 0.61/0.84  thf('41', plain,
% 0.61/0.84      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v1_xboole_0 @ 
% 0.61/0.84           (k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['40'])).
% 0.61/0.84  thf(fc4_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.84       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ A @ B ) ) ) ))).
% 0.61/0.84  thf('42', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i]:
% 0.61/0.84         ((v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.61/0.84      inference('cnf', [status(esa)], [fc4_xboole_0])).
% 0.61/0.84  thf('43', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['41', '42'])).
% 0.61/0.84  thf(t1_subset, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.61/0.84  thf('44', plain,
% 0.61/0.84      (![X10 : $i, X11 : $i]:
% 0.61/0.84         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.61/0.84      inference('cnf', [status(esa)], [t1_subset])).
% 0.61/0.84  thf('45', plain,
% 0.61/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.61/0.84  thf('46', plain,
% 0.61/0.84      (![X10 : $i, X11 : $i]:
% 0.61/0.84         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.61/0.84      inference('cnf', [status(esa)], [t1_subset])).
% 0.61/0.84  thf('47', plain,
% 0.61/0.84      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['45', '46'])).
% 0.61/0.84  thf('48', plain,
% 0.61/0.84      (![X26 : $i]:
% 0.61/0.84         (((X26) != (sk_D_1)) | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('49', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.61/0.84      inference('simplify', [status(thm)], ['48'])).
% 0.61/0.84  thf('50', plain,
% 0.61/0.84      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['47', '49'])).
% 0.61/0.84  thf('51', plain,
% 0.61/0.84      (![X27 : $i]:
% 0.61/0.84         (((X27) != (sk_D_1)) | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ sk_B_1)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('52', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('simplify', [status(thm)], ['51'])).
% 0.61/0.84  thf('53', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['50', '52'])).
% 0.61/0.84  thf(rc3_tops_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ?[B:$i]:
% 0.61/0.84         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.61/0.84           ( ~( v1_xboole_0 @ B ) ) & 
% 0.61/0.84           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.61/0.84  thf('54', plain,
% 0.61/0.84      (![X18 : $i]:
% 0.61/0.84         ((m1_subset_1 @ (sk_B @ X18) @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.61/0.84          | ~ (l1_pre_topc @ X18)
% 0.61/0.84          | ~ (v2_pre_topc @ X18)
% 0.61/0.84          | (v2_struct_0 @ X18))),
% 0.61/0.84      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.61/0.84  thf(cc1_subset_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( v1_xboole_0 @ A ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.61/0.84  thf('55', plain,
% 0.61/0.84      (![X8 : $i, X9 : $i]:
% 0.61/0.84         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.61/0.84          | (v1_xboole_0 @ X8)
% 0.61/0.84          | ~ (v1_xboole_0 @ X9))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.61/0.84  thf('56', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((v2_struct_0 @ X0)
% 0.61/0.84          | ~ (v2_pre_topc @ X0)
% 0.61/0.84          | ~ (l1_pre_topc @ X0)
% 0.61/0.84          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.84          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.61/0.84  thf('57', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B_1)
% 0.61/0.84        | ~ (v2_pre_topc @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['53', '56'])).
% 0.61/0.84  thf('58', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(dt_m1_pre_topc, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( l1_pre_topc @ A ) =>
% 0.61/0.84       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.61/0.84  thf('59', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i]:
% 0.61/0.84         (~ (m1_pre_topc @ X16 @ X17)
% 0.61/0.84          | (l1_pre_topc @ X16)
% 0.61/0.84          | ~ (l1_pre_topc @ X17))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.61/0.84  thf('60', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['58', '59'])).
% 0.61/0.84  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('62', plain, ((l1_pre_topc @ sk_B_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['60', '61'])).
% 0.61/0.84  thf('63', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(cc1_pre_topc, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.84       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.61/0.84  thf('64', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]:
% 0.61/0.84         (~ (m1_pre_topc @ X14 @ X15)
% 0.61/0.84          | (v2_pre_topc @ X14)
% 0.61/0.84          | ~ (l1_pre_topc @ X15)
% 0.61/0.84          | ~ (v2_pre_topc @ X15))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.61/0.84  thf('65', plain,
% 0.61/0.84      ((~ (v2_pre_topc @ sk_A)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.84        | (v2_pre_topc @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['63', '64'])).
% 0.61/0.84  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('68', plain, ((v2_pre_topc @ sk_B_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.61/0.84  thf('69', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.61/0.84        | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['57', '62', '68'])).
% 0.61/0.84  thf('70', plain,
% 0.61/0.84      (((v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('simplify', [status(thm)], ['69'])).
% 0.61/0.84  thf('71', plain,
% 0.61/0.84      (![X18 : $i]:
% 0.61/0.84         (~ (v1_xboole_0 @ (sk_B @ X18))
% 0.61/0.84          | ~ (l1_pre_topc @ X18)
% 0.61/0.84          | ~ (v2_pre_topc @ X18)
% 0.61/0.84          | (v2_struct_0 @ X18))),
% 0.61/0.84      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.61/0.84  thf('72', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1)
% 0.61/0.84        | ~ (v2_pre_topc @ sk_B_1)
% 0.61/0.84        | ~ (l1_pre_topc @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['70', '71'])).
% 0.61/0.84  thf('73', plain, ((v2_pre_topc @ sk_B_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.61/0.84  thf('74', plain, ((l1_pre_topc @ sk_B_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['60', '61'])).
% 0.61/0.84  thf('75', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_B_1)
% 0.61/0.84        | (v2_struct_0 @ sk_A)
% 0.61/0.84        | (v2_struct_0 @ sk_C)
% 0.61/0.84        | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.61/0.84  thf('76', plain,
% 0.61/0.84      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.61/0.84      inference('simplify', [status(thm)], ['75'])).
% 0.61/0.84  thf('77', plain, (~ (v2_struct_0 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('78', plain, (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.61/0.84      inference('clc', [status(thm)], ['76', '77'])).
% 0.61/0.84  thf('79', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 0.61/0.84      inference('clc', [status(thm)], ['78', '79'])).
% 0.61/0.84  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.61/0.85  
% 0.61/0.85  % SZS output end Refutation
% 0.61/0.85  
% 0.61/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
