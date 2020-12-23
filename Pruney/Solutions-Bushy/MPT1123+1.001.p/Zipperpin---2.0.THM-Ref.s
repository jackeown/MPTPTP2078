%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1123+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ipGpndhrcG

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 321 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          : 1736 (5932 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t54_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ( ~ ( v2_struct_0 @ A )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ~ ( ( v3_pre_topc @ D @ A )
                          & ( r2_hidden @ C @ D )
                          & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
                <=> ( ~ ( v2_struct_0 @ A )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( r2_hidden @ C @ D )
                            & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_pre_topc])).

thf('0',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('31',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ X23 )
      | ~ ( r1_xboole_0 @ sk_B @ X23 )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ~ ( r1_xboole_0 @ sk_B @ sk_D_1 )
      | ~ ( r2_hidden @ sk_C @ sk_D_1 )
      | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ sk_D_1 ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C @ sk_D_1 )
    | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('43',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d13_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( r1_xboole_0 @ B @ E )
                              & ( r2_hidden @ D @ E )
                              & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( v3_pre_topc @ E @ A )
        & ( r2_hidden @ D @ E )
        & ( r1_xboole_0 @ B @ E ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X3 @ X0 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_pre_topc @ X0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ sk_D_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_D_1 )
        | ( zip_tseitin_0 @ sk_D_1 @ X1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_D_1 @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X5 @ X6 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( zip_tseitin_0 @ sk_D_1 @ X0 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D_1 )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( r2_hidden @ sk_C @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_D_1 )
    | ~ ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','64'])).

thf('66',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k2_pre_topc @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X9 @ X5 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X9 @ X5 @ X6 )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('82',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('83',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k2_pre_topc @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('91',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference('sup-',[status(thm)],['80','91'])).

thf('93',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf('95',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X23 )
        | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ),
    inference(clc,[status(thm)],['95','98'])).

thf('100',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('102',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v2_struct_0 @ sk_A )
   <= ~ ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X23 )
          | ~ ( r1_xboole_0 @ sk_B @ X23 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','24','26','36','65','66','107'])).


%------------------------------------------------------------------------------
