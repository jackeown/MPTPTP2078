%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m7SHLUtMyX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:19 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  617 (64410 expanded)
%              Number of leaves         :   39 (17284 expanded)
%              Depth                    :   62
%              Number of atoms          : 5650 (1087798 expanded)
%              Number of equality atoms :  172 (8058 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t23_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) )
                      | ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) )).

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
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) )
                        | ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X36 ) )
      | ( m1_pre_topc @ X34 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( X25
       != ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( ( u1_struct_0 @ X25 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('30',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('33',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('34',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('38',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('39',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['4','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['3','55'])).

thf('57',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['26','27'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('61',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('68',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['26','27'])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('83',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('85',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['78','85'])).

thf('87',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['73','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('90',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('92',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('93',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('94',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['64','97'])).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('100',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('105',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('106',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('108',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('110',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('111',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('112',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('120',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('125',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('141',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('146',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('147',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('160',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','160'])).

thf('162',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['135','136'])).

thf('163',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('166',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('168',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','168'])).

thf('170',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('171',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('173',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('175',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('176',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('178',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['170','177'])).

thf('179',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('180',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['135','136'])).

thf('182',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('183',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('185',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('187',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('189',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['180','189'])).

thf('191',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('192',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('194',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('195',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('196',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','199'])).

thf('201',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('202',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','202'])).

thf('204',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('205',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['174','175'])).

thf('206',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('208',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('210',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('211',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('212',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['208','209','210','211'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['213','214'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('216',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['174','175'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['115','219'])).

thf('221',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('222',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('225',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['225'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('227',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('228',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('230',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('232',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('236',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['228','229','236'])).

thf('238',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('239',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('241',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('242',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['224','242'])).

thf('244',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('245',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['223','245'])).

thf('247',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('248',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('250',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['250','255'])).

thf('257',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A ),
    inference(clc,[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['263','264','265','266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('270',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('271',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('272',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['78','85'])).

thf('273',plain,
    ( ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['271','272'])).

thf('274',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('275',plain,
    ( ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('277',plain,
    ( ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('279',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('280',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('281',plain,
    ( ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['277','278','279','280'])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['285','290'])).

thf('292',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['268','269','270','284','296'])).

thf('298',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['249','297'])).

thf('299',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A ),
    inference(clc,[status(thm)],['259','260'])).

thf('300',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('301',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('305',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['298','305'])).

thf('307',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('308',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['308','309','310','311'])).

thf('313',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['313','314'])).

thf('316',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['315','316'])).

thf('318',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('319',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('320',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('321',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('323',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('327',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('328',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('329',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('331',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['329','330'])).

thf('332',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['326','332'])).

thf('334',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['334','335'])).

thf('337',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('338',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('340',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('341',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('342',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['338','339','340','341'])).

thf('343',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('345',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('346',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('347',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('349',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['344','350'])).

thf('352',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['352','353'])).

thf('355',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['343','354'])).

thf('356',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['355','356'])).

thf('358',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['320','357'])).

thf('359',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('360',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('361',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['319','360'])).

thf('362',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['334','335'])).

thf('363',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('364',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['362','363'])).

thf('365',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('366',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['364','365'])).

thf('367',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('368',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('369',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['361','368'])).

thf('370',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('371',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('372',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['355','356'])).

thf('373',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['371','372'])).

thf('374',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('375',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['373','374'])).

thf('376',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['370','375'])).

thf('377',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('378',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['376','377'])).

thf('379',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['376','377'])).

thf('380',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('381',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['334','335'])).

thf('383',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('384',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['382','383'])).

thf('385',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('386',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['384','385'])).

thf('387',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['364','365'])).

thf('388',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['386','387'])).

thf('389',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['381','388'])).

thf('390',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['378','389'])).

thf('391',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('393',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['391','392'])).

thf('394',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('395',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('396',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('397',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['393','394','395','396'])).

thf('398',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['397'])).

thf('399',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['398','399'])).

thf('401',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['369','400'])).

thf('402',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('403',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['401','402'])).

thf('404',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('405',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['403','404'])).

thf('406',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['318','405'])).

thf('407',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('408',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('409',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['406','407','408'])).

thf('410',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('411',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['409','410'])).

thf('412',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('413',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('414',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('415',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['411','412','413','414'])).

thf('416',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['415'])).

thf('417',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['416','417'])).

thf('419',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('420',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('421',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['419','420'])).

thf('422',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['421'])).

thf('423',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['418','422'])).

thf('424',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('425',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['423','424'])).

thf('426',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['317','425'])).

thf('427',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('428',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['426','427'])).

thf('429',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['248','428'])).

thf('430',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('431',plain,
    ( ( ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['429','430'])).

thf('432',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('433',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['416','417'])).

thf('434',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('435',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['431','432','433','434'])).

thf('436',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('437',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['331'])).

thf('438',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['436','437'])).

thf('439',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['438','439'])).

thf('441',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('442',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['440','441'])).

thf('443',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('444',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['442','443'])).

thf('445',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('446',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['444','445'])).

thf('447',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['440','441'])).

thf('448',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('449',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['447','448'])).

thf('450',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('451',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['449','450'])).

thf('452',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['446','451'])).

thf('453',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('454',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['452','453'])).

thf('455',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('456',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['440','441'])).

thf('457',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('458',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['456','457'])).

thf('459',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('460',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('462',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['458','459','460','461'])).

thf('463',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['462'])).

thf('464',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('465',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('466',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['349'])).

thf('467',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['465','466'])).

thf('468',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['467','468'])).

thf('470',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('471',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['469','470'])).

thf('472',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['463','464','471'])).

thf('473',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['455','472'])).

thf('474',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['449','450'])).

thf('475',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('476',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['474','475'])).

thf('477',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['473','476'])).

thf('478',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['416','417'])).

thf('479',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['477','478'])).

thf('480',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('481',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['479','480'])).

thf('482',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('483',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['232','233'])).

thf('484',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('485',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['481','482','483','484'])).

thf('486',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['485'])).

thf('487',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('488',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['486','487'])).

thf('489',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('490',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['488','489'])).

thf('491',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('492',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['488','489'])).

thf('493',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['454','490','491','492'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('494',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('495',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['493','494'])).

thf('496',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['435','495'])).

thf('497',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('498',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A ),
    inference(clc,[status(thm)],['259','260'])).

thf('499',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['315','316'])).

thf('500',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('501',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('502',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X36 ) )
      | ( m1_pre_topc @ X34 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('503',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['501','502'])).

thf('504',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_D_2 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ sk_D_2 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['500','503'])).

thf('505',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['499','504'])).

thf('506',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('507',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('508',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['505','506','507'])).

thf('509',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['498','508'])).

thf('510',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('511',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('512',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('513',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['509','510','511','512'])).

thf('514',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ sk_A ),
    inference(clc,[status(thm)],['259','260'])).

thf('515',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X36 )
      | ( r1_tarski @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('516',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['514','515'])).

thf('517',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('518',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('519',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['516','517','518'])).

thf('520',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['513','519'])).

thf('521',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('522',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('523',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['520','521','522'])).

thf('524',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('525',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['523','524'])).

thf('526',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['497','525'])).

thf('527',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['315','316'])).

thf('528',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('529',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('530',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['526','527','528','529'])).

thf('531',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['496','530'])).

thf('532',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('533',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('534',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['225'])).

thf('535',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('536',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['534','535'])).

thf('537',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('538',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('539',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['536','537','538'])).

thf('540',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['533','539'])).

thf('541',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('542',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['540','541'])).

thf('543',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['532','542'])).

thf('544',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('545',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['543','544'])).

thf('546',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['493','494'])).

thf('547',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['545','546'])).

thf('548',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('549',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('550',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('551',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['549','550'])).

thf('552',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['174','175'])).

thf('553',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('554',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['551','552','553'])).

thf('555',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('556',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['554','555'])).

thf('557',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('558',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('559',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['557','558'])).

thf('560',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('561',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['225'])).

thf('562',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['556','559','560','561'])).

thf('563',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['531','562'])).

thf('564',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['222','563'])).

thf('565',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('566',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['564','565'])).

thf('567',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('568',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['566','567'])).

thf('569',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','568'])).

thf('570',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['222','563'])).

thf('571',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('572',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['570','571'])).

thf('573',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['174','175'])).

thf('574',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('575',plain,(
    r1_tsep_1 @ sk_B @ sk_D_2 ),
    inference(demod,[status(thm)],['572','573','574'])).

thf('576',plain,(
    $false ),
    inference(demod,[status(thm)],['569','575'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m7SHLUtMyX
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.95/2.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.95/2.20  % Solved by: fo/fo7.sh
% 1.95/2.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.20  % done 3893 iterations in 1.738s
% 1.95/2.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.95/2.20  % SZS output start Refutation
% 1.95/2.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.95/2.20  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.95/2.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.95/2.20  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.95/2.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.95/2.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.95/2.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.95/2.20  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.95/2.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.95/2.20  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.95/2.20  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.95/2.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.95/2.20  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.95/2.20  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.95/2.20  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.95/2.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.95/2.20  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.95/2.20  thf(sk_B_type, type, sk_B: $i).
% 1.95/2.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.95/2.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.95/2.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.95/2.20  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.95/2.20  thf(t23_tmap_1, conjecture,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.20       ( ![B:$i]:
% 1.95/2.20         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.20           ( ![C:$i]:
% 1.95/2.20             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.20               ( ![D:$i]:
% 1.95/2.20                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.20                   ( ( m1_pre_topc @ B @ C ) =>
% 1.95/2.20                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 1.95/2.20                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 1.95/2.20                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.20  thf(zf_stmt_0, negated_conjecture,
% 1.95/2.20    (~( ![A:$i]:
% 1.95/2.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.95/2.20            ( l1_pre_topc @ A ) ) =>
% 1.95/2.20          ( ![B:$i]:
% 1.95/2.20            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.20              ( ![C:$i]:
% 1.95/2.20                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.20                  ( ![D:$i]:
% 1.95/2.20                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.20                      ( ( m1_pre_topc @ B @ C ) =>
% 1.95/2.20                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 1.95/2.20                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 1.95/2.20                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.95/2.20    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 1.95/2.20  thf('0', plain,
% 1.95/2.20      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('1', plain,
% 1.95/2.20      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 1.95/2.20      inference('split', [status(esa)], ['0'])).
% 1.95/2.20  thf(d3_struct_0, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.95/2.20  thf('2', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('3', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('4', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('5', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf(d10_xboole_0, axiom,
% 1.95/2.20    (![A:$i,B:$i]:
% 1.95/2.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.95/2.20  thf('6', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.95/2.20      inference('simplify', [status(thm)], ['6'])).
% 1.95/2.20  thf(t4_tsep_1, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.20       ( ![B:$i]:
% 1.95/2.20         ( ( m1_pre_topc @ B @ A ) =>
% 1.95/2.20           ( ![C:$i]:
% 1.95/2.20             ( ( m1_pre_topc @ C @ A ) =>
% 1.95/2.20               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.95/2.20                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.95/2.20  thf('8', plain,
% 1.95/2.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X34 @ X35)
% 1.95/2.20          | ~ (r1_tarski @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X36))
% 1.95/2.20          | (m1_pre_topc @ X34 @ X36)
% 1.95/2.20          | ~ (m1_pre_topc @ X36 @ X35)
% 1.95/2.20          | ~ (l1_pre_topc @ X35)
% 1.95/2.20          | ~ (v2_pre_topc @ X35))),
% 1.95/2.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.95/2.20  thf('9', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         (~ (v2_pre_topc @ X1)
% 1.95/2.20          | ~ (l1_pre_topc @ X1)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.20          | (m1_pre_topc @ X0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.95/2.20  thf('10', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         ((m1_pre_topc @ X0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.20          | ~ (l1_pre_topc @ X1)
% 1.95/2.20          | ~ (v2_pre_topc @ X1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['9'])).
% 1.95/2.20  thf('11', plain,
% 1.95/2.20      ((~ (v2_pre_topc @ sk_A)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['5', '10'])).
% 1.95/2.20  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('14', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('15', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf(dt_k1_tsep_1, axiom,
% 1.95/2.20    (![A:$i,B:$i,C:$i]:
% 1.95/2.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.95/2.20         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.95/2.20         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.20       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.95/2.20         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.95/2.20         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.95/2.20  thf('16', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('17', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.95/2.20  thf('18', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf(dt_m1_pre_topc, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( l1_pre_topc @ A ) =>
% 1.95/2.20       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.95/2.20  thf('19', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['18', '19'])).
% 1.95/2.20  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('22', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('23', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['17', '22'])).
% 1.95/2.20  thf('24', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2))),
% 1.95/2.20      inference('simplify', [status(thm)], ['23'])).
% 1.95/2.20  thf('25', plain,
% 1.95/2.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['14', '24'])).
% 1.95/2.20  thf('26', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2))),
% 1.95/2.20      inference('simplify', [status(thm)], ['25'])).
% 1.95/2.20  thf('27', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('28', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.95/2.20      inference('clc', [status(thm)], ['26', '27'])).
% 1.95/2.20  thf(d2_tsep_1, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.20       ( ![B:$i]:
% 1.95/2.20         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.20           ( ![C:$i]:
% 1.95/2.20             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.20               ( ![D:$i]:
% 1.95/2.20                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.95/2.20                     ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.20                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.95/2.20                     ( ( u1_struct_0 @ D ) =
% 1.95/2.20                       ( k2_xboole_0 @
% 1.95/2.20                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.20  thf('29', plain,
% 1.95/2.20      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.95/2.20         ((v2_struct_0 @ X23)
% 1.95/2.20          | ~ (m1_pre_topc @ X23 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X25)
% 1.95/2.20          | ~ (v1_pre_topc @ X25)
% 1.95/2.20          | ~ (m1_pre_topc @ X25 @ X24)
% 1.95/2.20          | ((X25) != (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | ((u1_struct_0 @ X25)
% 1.95/2.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.95/2.20          | ~ (m1_pre_topc @ X26 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X26)
% 1.95/2.20          | ~ (l1_pre_topc @ X24)
% 1.95/2.20          | (v2_struct_0 @ X24))),
% 1.95/2.20      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.95/2.20  thf('30', plain,
% 1.95/2.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.95/2.20         ((v2_struct_0 @ X24)
% 1.95/2.20          | ~ (l1_pre_topc @ X24)
% 1.95/2.20          | (v2_struct_0 @ X26)
% 1.95/2.20          | ~ (m1_pre_topc @ X26 @ X24)
% 1.95/2.20          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.95/2.20          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | ~ (m1_pre_topc @ X23 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X23))),
% 1.95/2.20      inference('simplify', [status(thm)], ['29'])).
% 1.95/2.20  thf('31', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['28', '30'])).
% 1.95/2.20  thf('32', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('33', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('34', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('35', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.95/2.20  thf('36', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('simplify', [status(thm)], ['35'])).
% 1.95/2.20  thf('37', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('38', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('39', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('40', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['38', '39'])).
% 1.95/2.20  thf('41', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('42', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['40', '41'])).
% 1.95/2.20  thf('43', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_D_2)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['42'])).
% 1.95/2.20  thf('44', plain,
% 1.95/2.20      (((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['37', '43'])).
% 1.95/2.20  thf('45', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['44'])).
% 1.95/2.20  thf('46', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('47', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['45', '46'])).
% 1.95/2.20  thf('48', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['36', '47'])).
% 1.95/2.20  thf('49', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('50', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))))),
% 1.95/2.20      inference('clc', [status(thm)], ['48', '49'])).
% 1.95/2.20  thf('51', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['4', '50'])).
% 1.95/2.20  thf('52', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf(dt_l1_pre_topc, axiom,
% 1.95/2.20    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.95/2.20  thf('53', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('54', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('55', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['51', '54'])).
% 1.95/2.20  thf('56', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['3', '55'])).
% 1.95/2.20  thf('57', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.95/2.20      inference('clc', [status(thm)], ['26', '27'])).
% 1.95/2.20  thf('58', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('59', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['57', '58'])).
% 1.95/2.20  thf('60', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('61', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['59', '60'])).
% 1.95/2.20  thf('62', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('63', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['61', '62'])).
% 1.95/2.20  thf('64', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['56', '63'])).
% 1.95/2.20  thf('65', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('66', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('67', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))))),
% 1.95/2.20      inference('clc', [status(thm)], ['48', '49'])).
% 1.95/2.20  thf('68', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['66', '67'])).
% 1.95/2.20  thf('69', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('70', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['68', '69'])).
% 1.95/2.20  thf('71', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['65', '70'])).
% 1.95/2.20  thf('72', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['61', '62'])).
% 1.95/2.20  thf('73', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['71', '72'])).
% 1.95/2.20  thf('74', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['71', '72'])).
% 1.95/2.20  thf(t7_xboole_1, axiom,
% 1.95/2.20    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.95/2.20  thf('75', plain,
% 1.95/2.20      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.95/2.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.20  thf('76', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('77', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.95/2.20          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['75', '76'])).
% 1.95/2.20  thf('78', plain,
% 1.95/2.20      ((~ (r1_tarski @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20           (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['74', '77'])).
% 1.95/2.20  thf('79', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.95/2.20      inference('clc', [status(thm)], ['26', '27'])).
% 1.95/2.20  thf(d9_pre_topc, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( l1_pre_topc @ A ) =>
% 1.95/2.20       ( ![B:$i]:
% 1.95/2.20         ( ( l1_pre_topc @ B ) =>
% 1.95/2.20           ( ( m1_pre_topc @ B @ A ) <=>
% 1.95/2.20             ( ( ![C:$i]:
% 1.95/2.20                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.95/2.20                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 1.95/2.20                     ( ?[D:$i]:
% 1.95/2.20                       ( ( m1_subset_1 @
% 1.95/2.20                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.95/2.20                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 1.95/2.20                         ( ( C ) =
% 1.95/2.20                           ( k9_subset_1 @
% 1.95/2.20                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 1.95/2.20               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 1.95/2.20  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.95/2.20  thf(zf_stmt_2, axiom,
% 1.95/2.20    (![D:$i,C:$i,B:$i,A:$i]:
% 1.95/2.20     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 1.95/2.20       ( ( ( C ) =
% 1.95/2.20           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 1.95/2.20         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 1.95/2.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.95/2.20  thf(zf_stmt_3, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( l1_pre_topc @ A ) =>
% 1.95/2.20       ( ![B:$i]:
% 1.95/2.20         ( ( l1_pre_topc @ B ) =>
% 1.95/2.20           ( ( m1_pre_topc @ B @ A ) <=>
% 1.95/2.20             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 1.95/2.20               ( ![C:$i]:
% 1.95/2.20                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.95/2.20                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 1.95/2.20                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.20  thf('80', plain,
% 1.95/2.20      (![X15 : $i, X16 : $i]:
% 1.95/2.20         (~ (l1_pre_topc @ X15)
% 1.95/2.20          | ~ (m1_pre_topc @ X15 @ X16)
% 1.95/2.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.95/2.20          | ~ (l1_pre_topc @ X16))),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.95/2.20  thf('81', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20        | (r1_tarski @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20           (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['79', '80'])).
% 1.95/2.20  thf('82', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('83', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20         (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['81', '82'])).
% 1.95/2.20  thf('84', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['59', '60'])).
% 1.95/2.20  thf('85', plain,
% 1.95/2.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20        (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['83', '84'])).
% 1.95/2.20  thf('86', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['78', '85'])).
% 1.95/2.20  thf('87', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['73', '86'])).
% 1.95/2.20  thf('88', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['87'])).
% 1.95/2.20  thf('89', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('90', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['88', '89'])).
% 1.95/2.20  thf('91', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('92', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('93', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('94', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 1.95/2.20  thf('95', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['94'])).
% 1.95/2.20  thf('96', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('97', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20         = (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['95', '96'])).
% 1.95/2.20  thf('98', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_D_2)
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['64', '97'])).
% 1.95/2.20  thf('99', plain,
% 1.95/2.20      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.95/2.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.20  thf('100', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['98', '99'])).
% 1.95/2.20  thf('101', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('102', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.95/2.20        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['100', '101'])).
% 1.95/2.20  thf('103', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['2', '102'])).
% 1.95/2.20  thf('104', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.95/2.20      inference('simplify', [status(thm)], ['6'])).
% 1.95/2.20  thf('105', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('106', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['103', '104', '105'])).
% 1.95/2.20  thf('107', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('108', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['106', '107'])).
% 1.95/2.20  thf('109', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('110', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('111', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('112', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 1.95/2.20  thf('113', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['112'])).
% 1.95/2.20  thf('114', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('115', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['113', '114'])).
% 1.95/2.20  thf('116', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('117', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('118', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('119', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         ((m1_pre_topc @ X0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.20          | ~ (l1_pre_topc @ X1)
% 1.95/2.20          | ~ (v2_pre_topc @ X1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['9'])).
% 1.95/2.20  thf('120', plain,
% 1.95/2.20      ((~ (v2_pre_topc @ sk_A)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | (m1_pre_topc @ sk_B @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['118', '119'])).
% 1.95/2.20  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('123', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('124', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('125', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('126', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_B)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['124', '125'])).
% 1.95/2.20  thf('127', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('128', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('129', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['127', '128'])).
% 1.95/2.20  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('132', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['126', '131'])).
% 1.95/2.20  thf('133', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B))),
% 1.95/2.20      inference('simplify', [status(thm)], ['132'])).
% 1.95/2.20  thf('134', plain,
% 1.95/2.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['123', '133'])).
% 1.95/2.20  thf('135', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B))),
% 1.95/2.20      inference('simplify', [status(thm)], ['134'])).
% 1.95/2.20  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('137', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 1.95/2.20      inference('clc', [status(thm)], ['135', '136'])).
% 1.95/2.20  thf('138', plain,
% 1.95/2.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.95/2.20         ((v2_struct_0 @ X24)
% 1.95/2.20          | ~ (l1_pre_topc @ X24)
% 1.95/2.20          | (v2_struct_0 @ X26)
% 1.95/2.20          | ~ (m1_pre_topc @ X26 @ X24)
% 1.95/2.20          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.95/2.20          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | ~ (m1_pre_topc @ X23 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X23))),
% 1.95/2.20      inference('simplify', [status(thm)], ['29'])).
% 1.95/2.20  thf('139', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['137', '138'])).
% 1.95/2.20  thf('140', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('141', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('143', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 1.95/2.20  thf('144', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('simplify', [status(thm)], ['143'])).
% 1.95/2.20  thf('145', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('146', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('147', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('148', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_B)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['146', '147'])).
% 1.95/2.20  thf('149', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('150', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['148', '149'])).
% 1.95/2.20  thf('151', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_B)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['150'])).
% 1.95/2.20  thf('152', plain,
% 1.95/2.20      (((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['145', '151'])).
% 1.95/2.20  thf('153', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B) | (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['152'])).
% 1.95/2.20  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('155', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.95/2.20      inference('clc', [status(thm)], ['153', '154'])).
% 1.95/2.20  thf('156', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['144', '155'])).
% 1.95/2.20  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('158', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.20      inference('clc', [status(thm)], ['156', '157'])).
% 1.95/2.20  thf('159', plain,
% 1.95/2.20      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.95/2.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.20  thf('160', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.20         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['158', '159'])).
% 1.95/2.20  thf('161', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.20         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['117', '160'])).
% 1.95/2.20  thf('162', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 1.95/2.20      inference('clc', [status(thm)], ['135', '136'])).
% 1.95/2.20  thf('163', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('164', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_B)
% 1.95/2.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['162', '163'])).
% 1.95/2.20  thf('165', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('166', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['164', '165'])).
% 1.95/2.20  thf('167', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('168', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['166', '167'])).
% 1.95/2.20  thf('169', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.20         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['161', '168'])).
% 1.95/2.20  thf('170', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('171', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('172', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.20         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['158', '159'])).
% 1.95/2.20  thf('173', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.95/2.20         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['171', '172'])).
% 1.95/2.20  thf('174', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('175', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('176', plain, ((l1_struct_0 @ sk_B)),
% 1.95/2.20      inference('sup-', [status(thm)], ['174', '175'])).
% 1.95/2.20  thf('177', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.95/2.20         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['173', '176'])).
% 1.95/2.20  thf('178', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.95/2.20         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['170', '177'])).
% 1.95/2.20  thf('179', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['166', '167'])).
% 1.95/2.20  thf('180', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.95/2.20         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['178', '179'])).
% 1.95/2.20  thf('181', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 1.95/2.20      inference('clc', [status(thm)], ['135', '136'])).
% 1.95/2.20  thf('182', plain,
% 1.95/2.20      (![X15 : $i, X16 : $i]:
% 1.95/2.20         (~ (l1_pre_topc @ X15)
% 1.95/2.20          | ~ (m1_pre_topc @ X15 @ X16)
% 1.95/2.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.95/2.20          | ~ (l1_pre_topc @ X16))),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.95/2.20  thf('183', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_B)
% 1.95/2.20        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 1.95/2.20           (k2_struct_0 @ sk_B))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['181', '182'])).
% 1.95/2.20  thf('184', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('185', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 1.95/2.20         (k2_struct_0 @ sk_B))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['183', '184'])).
% 1.95/2.20  thf('186', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['164', '165'])).
% 1.95/2.20  thf('187', plain,
% 1.95/2.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 1.95/2.20        (k2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['185', '186'])).
% 1.95/2.20  thf('188', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('189', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | ((k2_struct_0 @ sk_B)
% 1.95/2.20            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 1.95/2.20      inference('sup-', [status(thm)], ['187', '188'])).
% 1.95/2.20  thf('190', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ((k2_struct_0 @ sk_B)
% 1.95/2.20            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 1.95/2.20      inference('sup-', [status(thm)], ['180', '189'])).
% 1.95/2.20  thf('191', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('192', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_B)
% 1.95/2.20          = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['190', '191'])).
% 1.95/2.20  thf('193', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('194', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('195', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('196', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_B)
% 1.95/2.20          = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 1.95/2.20  thf('197', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | ((k2_struct_0 @ sk_B)
% 1.95/2.20            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 1.95/2.20      inference('simplify', [status(thm)], ['196'])).
% 1.95/2.20  thf('198', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('199', plain,
% 1.95/2.20      (((k2_struct_0 @ sk_B) = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('clc', [status(thm)], ['197', '198'])).
% 1.95/2.20  thf('200', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['169', '199'])).
% 1.95/2.20  thf('201', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('202', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.95/2.20        | ~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.95/2.20        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['200', '201'])).
% 1.95/2.20  thf('203', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_B)
% 1.95/2.20        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['116', '202'])).
% 1.95/2.20  thf('204', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.95/2.20      inference('simplify', [status(thm)], ['6'])).
% 1.95/2.20  thf('205', plain, ((l1_struct_0 @ sk_B)),
% 1.95/2.20      inference('sup-', [status(thm)], ['174', '175'])).
% 1.95/2.20  thf('206', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['203', '204', '205'])).
% 1.95/2.20  thf('207', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('208', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['206', '207'])).
% 1.95/2.20  thf('209', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('210', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['129', '130'])).
% 1.95/2.20  thf('211', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.95/2.20      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.95/2.20  thf('212', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['208', '209', '210', '211'])).
% 1.95/2.20  thf('213', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B) | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['212'])).
% 1.95/2.20  thf('214', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('215', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 1.95/2.20      inference('clc', [status(thm)], ['213', '214'])).
% 1.95/2.20  thf(d3_tsep_1, axiom,
% 1.95/2.20    (![A:$i]:
% 1.95/2.20     ( ( l1_struct_0 @ A ) =>
% 1.95/2.20       ( ![B:$i]:
% 1.95/2.20         ( ( l1_struct_0 @ B ) =>
% 1.95/2.20           ( ( r1_tsep_1 @ A @ B ) <=>
% 1.95/2.20             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.95/2.20  thf('216', plain,
% 1.95/2.20      (![X27 : $i, X28 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X27)
% 1.95/2.20          | ~ (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.95/2.20          | (r1_tsep_1 @ X28 @ X27)
% 1.95/2.20          | ~ (l1_struct_0 @ X28))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.95/2.20  thf('217', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | (r1_tsep_1 @ X0 @ sk_B)
% 1.95/2.20          | ~ (l1_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['215', '216'])).
% 1.95/2.20  thf('218', plain, ((l1_struct_0 @ sk_B)),
% 1.95/2.20      inference('sup-', [status(thm)], ['174', '175'])).
% 1.95/2.20  thf('219', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | (r1_tsep_1 @ X0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['217', '218'])).
% 1.95/2.20  thf('220', plain,
% 1.95/2.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 1.95/2.20        | (r1_tsep_1 @ sk_D_2 @ sk_B)
% 1.95/2.20        | ~ (l1_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['115', '219'])).
% 1.95/2.20  thf('221', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('222', plain,
% 1.95/2.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 1.95/2.20        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['220', '221'])).
% 1.95/2.20  thf('223', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('224', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('225', plain,
% 1.95/2.20      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('226', plain,
% 1.95/2.20      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('split', [status(esa)], ['225'])).
% 1.95/2.20  thf(symmetry_r1_tsep_1, axiom,
% 1.95/2.20    (![A:$i,B:$i]:
% 1.95/2.20     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 1.95/2.20       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 1.95/2.20  thf('227', plain,
% 1.95/2.20      (![X32 : $i, X33 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X32)
% 1.95/2.20          | ~ (l1_struct_0 @ X33)
% 1.95/2.20          | (r1_tsep_1 @ X33 @ X32)
% 1.95/2.20          | ~ (r1_tsep_1 @ X32 @ X33))),
% 1.95/2.20      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.95/2.20  thf('228', plain,
% 1.95/2.20      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 1.95/2.20         | ~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['226', '227'])).
% 1.95/2.20  thf('229', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('230', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('231', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('232', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['230', '231'])).
% 1.95/2.20  thf('233', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('234', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('235', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('236', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('237', plain,
% 1.95/2.20      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['228', '229', '236'])).
% 1.95/2.20  thf('238', plain,
% 1.95/2.20      (![X27 : $i, X28 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X27)
% 1.95/2.20          | ~ (r1_tsep_1 @ X28 @ X27)
% 1.95/2.20          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.95/2.20          | ~ (l1_struct_0 @ X28))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.95/2.20  thf('239', plain,
% 1.95/2.20      (((~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['237', '238'])).
% 1.95/2.20  thf('240', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('241', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('242', plain,
% 1.95/2.20      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['239', '240', '241'])).
% 1.95/2.20  thf('243', plain,
% 1.95/2.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['224', '242'])).
% 1.95/2.20  thf('244', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('245', plain,
% 1.95/2.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['243', '244'])).
% 1.95/2.20  thf('246', plain,
% 1.95/2.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['223', '245'])).
% 1.95/2.20  thf('247', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('248', plain,
% 1.95/2.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['246', '247'])).
% 1.95/2.20  thf('249', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('250', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('251', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('252', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('253', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ X0) @ sk_A)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_A)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['251', '252'])).
% 1.95/2.20  thf('254', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('255', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ X0) @ sk_A)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['253', '254'])).
% 1.95/2.20  thf('256', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A))),
% 1.95/2.20      inference('sup-', [status(thm)], ['250', '255'])).
% 1.95/2.20  thf('257', plain,
% 1.95/2.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('simplify', [status(thm)], ['256'])).
% 1.95/2.20  thf('258', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('259', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A))),
% 1.95/2.20      inference('clc', [status(thm)], ['257', '258'])).
% 1.95/2.20  thf('260', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('261', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A)),
% 1.95/2.20      inference('clc', [status(thm)], ['259', '260'])).
% 1.95/2.20  thf('262', plain,
% 1.95/2.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.95/2.20         ((v2_struct_0 @ X24)
% 1.95/2.20          | ~ (l1_pre_topc @ X24)
% 1.95/2.20          | (v2_struct_0 @ X26)
% 1.95/2.20          | ~ (m1_pre_topc @ X26 @ X24)
% 1.95/2.20          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.95/2.20          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | ~ (m1_pre_topc @ X23 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X23))),
% 1.95/2.20      inference('simplify', [status(thm)], ['29'])).
% 1.95/2.20  thf('263', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_A))),
% 1.95/2.20      inference('sup-', [status(thm)], ['261', '262'])).
% 1.95/2.20  thf('264', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('265', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('266', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('267', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_A))),
% 1.95/2.20      inference('demod', [status(thm)], ['263', '264', '265', '266'])).
% 1.95/2.20  thf('268', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_A)
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('simplify', [status(thm)], ['267'])).
% 1.95/2.20  thf('269', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['113', '114'])).
% 1.95/2.20  thf('270', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['113', '114'])).
% 1.95/2.20  thf('271', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('272', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['78', '85'])).
% 1.95/2.20  thf('273', plain,
% 1.95/2.20      ((((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['271', '272'])).
% 1.95/2.20  thf('274', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('275', plain,
% 1.95/2.20      ((((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['273', '274'])).
% 1.95/2.20  thf('276', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('277', plain,
% 1.95/2.20      ((((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['275', '276'])).
% 1.95/2.20  thf('278', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('279', plain, ((l1_pre_topc @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.95/2.20  thf('280', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.95/2.20  thf('281', plain,
% 1.95/2.20      ((((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['277', '278', '279', '280'])).
% 1.95/2.20  thf('282', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['281'])).
% 1.95/2.20  thf('283', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('284', plain,
% 1.95/2.20      (((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20         = (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['282', '283'])).
% 1.95/2.20  thf('285', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('286', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('287', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('288', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_A)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['286', '287'])).
% 1.95/2.20  thf('289', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('290', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_A)
% 1.95/2.20          | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['288', '289'])).
% 1.95/2.20  thf('291', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['285', '290'])).
% 1.95/2.20  thf('292', plain,
% 1.95/2.20      (((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('simplify', [status(thm)], ['291'])).
% 1.95/2.20  thf('293', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('294', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('clc', [status(thm)], ['292', '293'])).
% 1.95/2.20  thf('295', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('296', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['294', '295'])).
% 1.95/2.20  thf('297', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_A)
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['268', '269', '270', '284', '296'])).
% 1.95/2.20  thf('298', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_A))),
% 1.95/2.20      inference('sup+', [status(thm)], ['249', '297'])).
% 1.95/2.20  thf('299', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A)),
% 1.95/2.20      inference('clc', [status(thm)], ['259', '260'])).
% 1.95/2.20  thf('300', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('301', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['299', '300'])).
% 1.95/2.20  thf('302', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('303', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['301', '302'])).
% 1.95/2.20  thf('304', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('305', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['303', '304'])).
% 1.95/2.20  thf('306', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_A))),
% 1.95/2.20      inference('demod', [status(thm)], ['298', '305'])).
% 1.95/2.20  thf('307', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('308', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_A)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_A))),
% 1.95/2.20      inference('sup-', [status(thm)], ['306', '307'])).
% 1.95/2.20  thf('309', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('310', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('311', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('312', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_A)
% 1.95/2.20        | (v2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['308', '309', '310', '311'])).
% 1.95/2.20  thf('313', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20          = (k2_struct_0 @ sk_D_2))
% 1.95/2.20        | (v2_struct_0 @ sk_D_2)
% 1.95/2.20        | (v2_struct_0 @ sk_A))),
% 1.95/2.20      inference('simplify', [status(thm)], ['312'])).
% 1.95/2.20  thf('314', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('315', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_A)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20            = (k2_struct_0 @ sk_D_2)))),
% 1.95/2.20      inference('clc', [status(thm)], ['313', '314'])).
% 1.95/2.20  thf('316', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('317', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20         = (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['315', '316'])).
% 1.95/2.20  thf('318', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('319', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('320', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('321', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('322', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         ((m1_pre_topc @ X0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.20          | ~ (l1_pre_topc @ X1)
% 1.95/2.20          | ~ (v2_pre_topc @ X1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['9'])).
% 1.95/2.20  thf('323', plain,
% 1.95/2.20      ((~ (v2_pre_topc @ sk_A)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['321', '322'])).
% 1.95/2.20  thf('324', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('325', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('326', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('327', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('328', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('329', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['327', '328'])).
% 1.95/2.20  thf('330', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('331', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['329', '330'])).
% 1.95/2.20  thf('332', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['331'])).
% 1.95/2.20  thf('333', plain,
% 1.95/2.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['326', '332'])).
% 1.95/2.20  thf('334', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['333'])).
% 1.95/2.20  thf('335', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('336', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 1.95/2.20      inference('clc', [status(thm)], ['334', '335'])).
% 1.95/2.20  thf('337', plain,
% 1.95/2.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.95/2.20         ((v2_struct_0 @ X24)
% 1.95/2.20          | ~ (l1_pre_topc @ X24)
% 1.95/2.20          | (v2_struct_0 @ X26)
% 1.95/2.20          | ~ (m1_pre_topc @ X26 @ X24)
% 1.95/2.20          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.95/2.20          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | ~ (m1_pre_topc @ X23 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X23))),
% 1.95/2.20      inference('simplify', [status(thm)], ['29'])).
% 1.95/2.20  thf('338', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['336', '337'])).
% 1.95/2.20  thf('339', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('340', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('341', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('342', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['338', '339', '340', '341'])).
% 1.95/2.20  thf('343', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['342'])).
% 1.95/2.20  thf('344', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('345', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('346', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('347', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['345', '346'])).
% 1.95/2.20  thf('348', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('349', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['347', '348'])).
% 1.95/2.20  thf('350', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['349'])).
% 1.95/2.20  thf('351', plain,
% 1.95/2.20      (((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['344', '350'])).
% 1.95/2.20  thf('352', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['351'])).
% 1.95/2.20  thf('353', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('354', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('clc', [status(thm)], ['352', '353'])).
% 1.95/2.20  thf('355', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['343', '354'])).
% 1.95/2.20  thf('356', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('357', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))))),
% 1.95/2.20      inference('clc', [status(thm)], ['355', '356'])).
% 1.95/2.20  thf('358', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['320', '357'])).
% 1.95/2.20  thf('359', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('360', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['358', '359'])).
% 1.95/2.20  thf('361', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['319', '360'])).
% 1.95/2.20  thf('362', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 1.95/2.20      inference('clc', [status(thm)], ['334', '335'])).
% 1.95/2.20  thf('363', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('364', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['362', '363'])).
% 1.95/2.20  thf('365', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('366', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['364', '365'])).
% 1.95/2.20  thf('367', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('368', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['366', '367'])).
% 1.95/2.20  thf('369', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['361', '368'])).
% 1.95/2.20  thf('370', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('371', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('372', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))))),
% 1.95/2.20      inference('clc', [status(thm)], ['355', '356'])).
% 1.95/2.20  thf('373', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['371', '372'])).
% 1.95/2.20  thf('374', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('375', plain,
% 1.95/2.20      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['373', '374'])).
% 1.95/2.20  thf('376', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['370', '375'])).
% 1.95/2.20  thf('377', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['366', '367'])).
% 1.95/2.20  thf('378', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['376', '377'])).
% 1.95/2.20  thf('379', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['376', '377'])).
% 1.95/2.20  thf('380', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.95/2.20          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['75', '76'])).
% 1.95/2.20  thf('381', plain,
% 1.95/2.20      ((~ (r1_tarski @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.95/2.20           (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20            = (k2_struct_0 @ sk_C_1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['379', '380'])).
% 1.95/2.20  thf('382', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 1.95/2.20      inference('clc', [status(thm)], ['334', '335'])).
% 1.95/2.20  thf('383', plain,
% 1.95/2.20      (![X15 : $i, X16 : $i]:
% 1.95/2.20         (~ (l1_pre_topc @ X15)
% 1.95/2.20          | ~ (m1_pre_topc @ X15 @ X16)
% 1.95/2.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.95/2.20          | ~ (l1_pre_topc @ X16))),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.95/2.20  thf('384', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (r1_tarski @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.95/2.20           (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['382', '383'])).
% 1.95/2.20  thf('385', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('386', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.95/2.20         (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['384', '385'])).
% 1.95/2.20  thf('387', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['364', '365'])).
% 1.95/2.20  thf('388', plain,
% 1.95/2.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.95/2.20        (k2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['386', '387'])).
% 1.95/2.20  thf('389', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20            = (k2_struct_0 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['381', '388'])).
% 1.95/2.20  thf('390', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['378', '389'])).
% 1.95/2.20  thf('391', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20            = (k2_struct_0 @ sk_C_1)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['390'])).
% 1.95/2.20  thf('392', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('393', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['391', '392'])).
% 1.95/2.20  thf('394', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('395', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('396', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('397', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20          = (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['393', '394', '395', '396'])).
% 1.95/2.20  thf('398', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20            = (k2_struct_0 @ sk_C_1)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['397'])).
% 1.95/2.20  thf('399', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('400', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20         = (k2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('clc', [status(thm)], ['398', '399'])).
% 1.95/2.20  thf('401', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_C_1)
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['369', '400'])).
% 1.95/2.20  thf('402', plain,
% 1.95/2.20      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.95/2.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.20  thf('403', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['401', '402'])).
% 1.95/2.20  thf('404', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('405', plain,
% 1.95/2.20      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.95/2.20        | ~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['403', '404'])).
% 1.95/2.20  thf('406', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (l1_struct_0 @ sk_C_1)
% 1.95/2.20        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['318', '405'])).
% 1.95/2.20  thf('407', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.95/2.20      inference('simplify', [status(thm)], ['6'])).
% 1.95/2.20  thf('408', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('409', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['406', '407', '408'])).
% 1.95/2.20  thf('410', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('411', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['409', '410'])).
% 1.95/2.20  thf('412', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('413', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('414', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('415', plain,
% 1.95/2.20      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['411', '412', '413', '414'])).
% 1.95/2.20  thf('416', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['415'])).
% 1.95/2.20  thf('417', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('418', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('clc', [status(thm)], ['416', '417'])).
% 1.95/2.20  thf('419', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('420', plain,
% 1.95/2.20      (![X27 : $i, X28 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X27)
% 1.95/2.20          | ~ (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.95/2.20          | (r1_tsep_1 @ X28 @ X27)
% 1.95/2.20          | ~ (l1_struct_0 @ X28))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.95/2.20  thf('421', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | (r1_tsep_1 @ X0 @ X1)
% 1.95/2.20          | ~ (l1_struct_0 @ X1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['419', '420'])).
% 1.95/2.20  thf('422', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X1)
% 1.95/2.20          | (r1_tsep_1 @ X0 @ X1)
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['421'])).
% 1.95/2.20  thf('423', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | (r1_tsep_1 @ X0 @ sk_C_1)
% 1.95/2.20          | ~ (l1_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['418', '422'])).
% 1.95/2.20  thf('424', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('425', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | (r1_tsep_1 @ X0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['423', '424'])).
% 1.95/2.20  thf('426', plain,
% 1.95/2.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_C_1)
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['317', '425'])).
% 1.95/2.20  thf('427', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['303', '304'])).
% 1.95/2.20  thf('428', plain,
% 1.95/2.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['426', '427'])).
% 1.95/2.20  thf('429', plain,
% 1.95/2.20      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_C_1))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['248', '428'])).
% 1.95/2.20  thf('430', plain,
% 1.95/2.20      (![X27 : $i, X28 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X27)
% 1.95/2.20          | ~ (r1_tsep_1 @ X28 @ X27)
% 1.95/2.20          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.95/2.20          | ~ (l1_struct_0 @ X28))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.95/2.20  thf('431', plain,
% 1.95/2.20      (((~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20         | (r1_xboole_0 @ 
% 1.95/2.20            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20            (u1_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['429', '430'])).
% 1.95/2.20  thf('432', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['303', '304'])).
% 1.95/2.20  thf('433', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('clc', [status(thm)], ['416', '417'])).
% 1.95/2.20  thf('434', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('435', plain,
% 1.95/2.20      (((r1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20         (k2_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['431', '432', '433', '434'])).
% 1.95/2.20  thf('436', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('437', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['331'])).
% 1.95/2.20  thf('438', plain,
% 1.95/2.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['436', '437'])).
% 1.95/2.20  thf('439', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('440', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1))),
% 1.95/2.20      inference('clc', [status(thm)], ['438', '439'])).
% 1.95/2.20  thf('441', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('442', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 1.95/2.20      inference('clc', [status(thm)], ['440', '441'])).
% 1.95/2.20  thf('443', plain,
% 1.95/2.20      (![X15 : $i, X16 : $i]:
% 1.95/2.20         (~ (l1_pre_topc @ X15)
% 1.95/2.20          | ~ (m1_pre_topc @ X15 @ X16)
% 1.95/2.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.95/2.20          | ~ (l1_pre_topc @ X16))),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.95/2.20  thf('444', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 1.95/2.20           (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['442', '443'])).
% 1.95/2.20  thf('445', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('446', plain,
% 1.95/2.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 1.95/2.20         (k2_struct_0 @ sk_C_1))
% 1.95/2.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['444', '445'])).
% 1.95/2.20  thf('447', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 1.95/2.20      inference('clc', [status(thm)], ['440', '441'])).
% 1.95/2.20  thf('448', plain,
% 1.95/2.20      (![X21 : $i, X22 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X21 @ X22)
% 1.95/2.20          | (l1_pre_topc @ X21)
% 1.95/2.20          | ~ (l1_pre_topc @ X22))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.20  thf('449', plain,
% 1.95/2.20      ((~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['447', '448'])).
% 1.95/2.20  thf('450', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('451', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['449', '450'])).
% 1.95/2.20  thf('452', plain,
% 1.95/2.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 1.95/2.20        (k2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['446', '451'])).
% 1.95/2.20  thf('453', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('454', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))
% 1.95/2.20        | ((k2_struct_0 @ sk_C_1)
% 1.95/2.20            = (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))))),
% 1.95/2.20      inference('sup-', [status(thm)], ['452', '453'])).
% 1.95/2.20  thf('455', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('456', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 1.95/2.20      inference('clc', [status(thm)], ['440', '441'])).
% 1.95/2.20  thf('457', plain,
% 1.95/2.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.95/2.20         ((v2_struct_0 @ X24)
% 1.95/2.20          | ~ (l1_pre_topc @ X24)
% 1.95/2.20          | (v2_struct_0 @ X26)
% 1.95/2.20          | ~ (m1_pre_topc @ X26 @ X24)
% 1.95/2.20          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.95/2.20          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.95/2.20          | ~ (m1_pre_topc @ X23 @ X24)
% 1.95/2.20          | (v2_struct_0 @ X23))),
% 1.95/2.20      inference('simplify', [status(thm)], ['29'])).
% 1.95/2.20  thf('458', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['456', '457'])).
% 1.95/2.20  thf('459', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('460', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('461', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('462', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['458', '459', '460', '461'])).
% 1.95/2.20  thf('463', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 1.95/2.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('simplify', [status(thm)], ['462'])).
% 1.95/2.20  thf('464', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 1.95/2.20      inference('clc', [status(thm)], ['213', '214'])).
% 1.95/2.20  thf('465', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('466', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         ((v2_struct_0 @ sk_C_1)
% 1.95/2.20          | (v2_struct_0 @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.95/2.20          | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0)))),
% 1.95/2.20      inference('simplify', [status(thm)], ['349'])).
% 1.95/2.20  thf('467', plain,
% 1.95/2.20      (((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['465', '466'])).
% 1.95/2.20  thf('468', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('469', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.95/2.20      inference('clc', [status(thm)], ['467', '468'])).
% 1.95/2.20  thf('470', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('471', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.95/2.20      inference('clc', [status(thm)], ['469', '470'])).
% 1.95/2.20  thf('472', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['463', '464', '471'])).
% 1.95/2.20  thf('473', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('sup+', [status(thm)], ['455', '472'])).
% 1.95/2.20  thf('474', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['449', '450'])).
% 1.95/2.20  thf('475', plain,
% 1.95/2.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.20  thf('476', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.95/2.20      inference('sup-', [status(thm)], ['474', '475'])).
% 1.95/2.20  thf('477', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['473', '476'])).
% 1.95/2.20  thf('478', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('clc', [status(thm)], ['416', '417'])).
% 1.95/2.20  thf('479', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('demod', [status(thm)], ['477', '478'])).
% 1.95/2.20  thf('480', plain,
% 1.95/2.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X29)
% 1.95/2.20          | ~ (l1_pre_topc @ X30)
% 1.95/2.20          | (v2_struct_0 @ X30)
% 1.95/2.20          | (v2_struct_0 @ X31)
% 1.95/2.20          | ~ (m1_pre_topc @ X31 @ X30)
% 1.95/2.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.95/2.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.95/2.20  thf('481', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.95/2.20      inference('sup-', [status(thm)], ['479', '480'])).
% 1.95/2.20  thf('482', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('483', plain, ((l1_pre_topc @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['232', '233'])).
% 1.95/2.20  thf('484', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.95/2.20      inference('demod', [status(thm)], ['323', '324', '325'])).
% 1.95/2.20  thf('485', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_B)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_C_1))),
% 1.95/2.20      inference('demod', [status(thm)], ['481', '482', '483', '484'])).
% 1.95/2.20  thf('486', plain,
% 1.95/2.20      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20        | (v2_struct_0 @ sk_C_1)
% 1.95/2.20        | (v2_struct_0 @ sk_B))),
% 1.95/2.20      inference('simplify', [status(thm)], ['485'])).
% 1.95/2.20  thf('487', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('488', plain,
% 1.95/2.20      (((v2_struct_0 @ sk_B)
% 1.95/2.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))))),
% 1.95/2.20      inference('clc', [status(thm)], ['486', '487'])).
% 1.95/2.20  thf('489', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('490', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 1.95/2.20      inference('clc', [status(thm)], ['488', '489'])).
% 1.95/2.20  thf('491', plain,
% 1.95/2.20      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.95/2.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.95/2.20  thf('492', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.95/2.20         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 1.95/2.20      inference('clc', [status(thm)], ['488', '489'])).
% 1.95/2.20  thf('493', plain,
% 1.95/2.20      (((k2_struct_0 @ sk_C_1)
% 1.95/2.20         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 1.95/2.20      inference('demod', [status(thm)], ['454', '490', '491', '492'])).
% 1.95/2.20  thf(t70_xboole_1, axiom,
% 1.95/2.20    (![A:$i,B:$i,C:$i]:
% 1.95/2.20     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.95/2.20            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.95/2.20       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.95/2.20            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.95/2.20  thf('494', plain,
% 1.95/2.20      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.95/2.20         ((r1_xboole_0 @ X3 @ X6)
% 1.95/2.20          | ~ (r1_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X6)))),
% 1.95/2.20      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.95/2.20  thf('495', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['493', '494'])).
% 1.95/2.20  thf('496', plain,
% 1.95/2.20      (((r1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20         (k2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['435', '495'])).
% 1.95/2.20  thf('497', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('498', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A)),
% 1.95/2.20      inference('clc', [status(thm)], ['259', '260'])).
% 1.95/2.20  thf('499', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20         = (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['315', '316'])).
% 1.95/2.20  thf('500', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['113', '114'])).
% 1.95/2.20  thf('501', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('502', plain,
% 1.95/2.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X34 @ X35)
% 1.95/2.20          | ~ (r1_tarski @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X36))
% 1.95/2.20          | (m1_pre_topc @ X34 @ X36)
% 1.95/2.20          | ~ (m1_pre_topc @ X36 @ X35)
% 1.95/2.20          | ~ (l1_pre_topc @ X35)
% 1.95/2.20          | ~ (v2_pre_topc @ X35))),
% 1.95/2.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.95/2.20  thf('503', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.20         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.95/2.20          | ~ (l1_struct_0 @ X0)
% 1.95/2.20          | ~ (v2_pre_topc @ X2)
% 1.95/2.20          | ~ (l1_pre_topc @ X2)
% 1.95/2.20          | ~ (m1_pre_topc @ X1 @ X2)
% 1.95/2.20          | (m1_pre_topc @ X0 @ X1)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['501', '502'])).
% 1.95/2.20  thf('504', plain,
% 1.95/2.20      (![X0 : $i, X1 : $i]:
% 1.95/2.20         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.20          | (m1_pre_topc @ X0 @ sk_D_2)
% 1.95/2.20          | ~ (m1_pre_topc @ sk_D_2 @ X1)
% 1.95/2.20          | ~ (l1_pre_topc @ X1)
% 1.95/2.20          | ~ (v2_pre_topc @ X1)
% 1.95/2.20          | ~ (l1_struct_0 @ X0))),
% 1.95/2.20      inference('sup-', [status(thm)], ['500', '503'])).
% 1.95/2.20  thf('505', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.95/2.20          | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20          | ~ (v2_pre_topc @ X0)
% 1.95/2.20          | ~ (l1_pre_topc @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ sk_D_2 @ X0)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ X0))),
% 1.95/2.20      inference('sup-', [status(thm)], ['499', '504'])).
% 1.95/2.20  thf('506', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.95/2.20      inference('simplify', [status(thm)], ['6'])).
% 1.95/2.20  thf('507', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['303', '304'])).
% 1.95/2.20  thf('508', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (v2_pre_topc @ X0)
% 1.95/2.20          | ~ (l1_pre_topc @ X0)
% 1.95/2.20          | ~ (m1_pre_topc @ sk_D_2 @ X0)
% 1.95/2.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ X0))),
% 1.95/2.20      inference('demod', [status(thm)], ['505', '506', '507'])).
% 1.95/2.20  thf('509', plain,
% 1.95/2.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_A)
% 1.95/2.20        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20        | ~ (v2_pre_topc @ sk_A))),
% 1.95/2.20      inference('sup-', [status(thm)], ['498', '508'])).
% 1.95/2.20  thf('510', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('511', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('512', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('513', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.95/2.20      inference('demod', [status(thm)], ['509', '510', '511', '512'])).
% 1.95/2.20  thf('514', plain,
% 1.95/2.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ sk_A)),
% 1.95/2.20      inference('clc', [status(thm)], ['259', '260'])).
% 1.95/2.20  thf('515', plain,
% 1.95/2.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X34 @ X35)
% 1.95/2.20          | ~ (m1_pre_topc @ X34 @ X36)
% 1.95/2.20          | (r1_tarski @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X36))
% 1.95/2.20          | ~ (m1_pre_topc @ X36 @ X35)
% 1.95/2.20          | ~ (l1_pre_topc @ X35)
% 1.95/2.20          | ~ (v2_pre_topc @ X35))),
% 1.95/2.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.95/2.20  thf('516', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (v2_pre_topc @ sk_A)
% 1.95/2.20          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.20          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.20          | (r1_tarski @ 
% 1.95/2.20             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20             (u1_struct_0 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ X0))),
% 1.95/2.20      inference('sup-', [status(thm)], ['514', '515'])).
% 1.95/2.20  thf('517', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('518', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('519', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.20          | (r1_tarski @ 
% 1.95/2.20             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20             (u1_struct_0 @ X0))
% 1.95/2.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2) @ X0))),
% 1.95/2.20      inference('demod', [status(thm)], ['516', '517', '518'])).
% 1.95/2.20  thf('520', plain,
% 1.95/2.20      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20         (u1_struct_0 @ sk_D_2))
% 1.95/2.20        | ~ (m1_pre_topc @ sk_D_2 @ sk_A))),
% 1.95/2.20      inference('sup-', [status(thm)], ['513', '519'])).
% 1.95/2.20  thf('521', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['113', '114'])).
% 1.95/2.20  thf('522', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.95/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.20  thf('523', plain,
% 1.95/2.20      ((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)) @ 
% 1.95/2.20        (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('demod', [status(thm)], ['520', '521', '522'])).
% 1.95/2.20  thf('524', plain,
% 1.95/2.20      (![X0 : $i, X2 : $i]:
% 1.95/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.95/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.20  thf('525', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ 
% 1.95/2.20           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))
% 1.95/2.20        | ((k2_struct_0 @ sk_D_2)
% 1.95/2.20            = (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))))),
% 1.95/2.20      inference('sup-', [status(thm)], ['523', '524'])).
% 1.95/2.20  thf('526', plain,
% 1.95/2.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ 
% 1.95/2.20           (k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))
% 1.95/2.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20        | ((k2_struct_0 @ sk_D_2)
% 1.95/2.20            = (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))))),
% 1.95/2.20      inference('sup-', [status(thm)], ['497', '525'])).
% 1.95/2.20  thf('527', plain,
% 1.95/2.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))
% 1.95/2.20         = (k2_struct_0 @ sk_D_2))),
% 1.95/2.20      inference('clc', [status(thm)], ['315', '316'])).
% 1.95/2.20  thf('528', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.95/2.20      inference('simplify', [status(thm)], ['6'])).
% 1.95/2.20  thf('529', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2))),
% 1.95/2.20      inference('sup-', [status(thm)], ['303', '304'])).
% 1.95/2.20  thf('530', plain,
% 1.95/2.20      (((k2_struct_0 @ sk_D_2)
% 1.95/2.20         = (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D_2 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['526', '527', '528', '529'])).
% 1.95/2.20  thf('531', plain,
% 1.95/2.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.95/2.20      inference('demod', [status(thm)], ['496', '530'])).
% 1.95/2.20  thf('532', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('533', plain,
% 1.95/2.20      (![X9 : $i]:
% 1.95/2.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.95/2.20  thf('534', plain,
% 1.95/2.20      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('split', [status(esa)], ['225'])).
% 1.95/2.20  thf('535', plain,
% 1.95/2.20      (![X27 : $i, X28 : $i]:
% 1.95/2.20         (~ (l1_struct_0 @ X27)
% 1.95/2.20          | ~ (r1_tsep_1 @ X28 @ X27)
% 1.95/2.20          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.95/2.20          | ~ (l1_struct_0 @ X28))),
% 1.95/2.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.95/2.20  thf('536', plain,
% 1.95/2.20      (((~ (l1_struct_0 @ sk_D_2)
% 1.95/2.20         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['534', '535'])).
% 1.95/2.20  thf('537', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('538', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('539', plain,
% 1.95/2.20      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['536', '537', '538'])).
% 1.95/2.20  thf('540', plain,
% 1.95/2.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['533', '539'])).
% 1.95/2.20  thf('541', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.20      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.20  thf('542', plain,
% 1.95/2.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['540', '541'])).
% 1.95/2.20  thf('543', plain,
% 1.95/2.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('sup+', [status(thm)], ['532', '542'])).
% 1.95/2.20  thf('544', plain, ((l1_struct_0 @ sk_C_1)),
% 1.95/2.20      inference('sup-', [status(thm)], ['234', '235'])).
% 1.95/2.20  thf('545', plain,
% 1.95/2.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 1.95/2.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.20      inference('demod', [status(thm)], ['543', '544'])).
% 1.95/2.20  thf('546', plain,
% 1.95/2.20      (![X0 : $i]:
% 1.95/2.20         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 1.95/2.20          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 1.95/2.20      inference('sup-', [status(thm)], ['493', '494'])).
% 1.95/2.20  thf('547', plain,
% 1.95/2.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 1.95/2.21         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.21      inference('sup-', [status(thm)], ['545', '546'])).
% 1.95/2.21  thf('548', plain,
% 1.95/2.21      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 1.95/2.21        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.95/2.21      inference('demod', [status(thm)], ['220', '221'])).
% 1.95/2.21  thf('549', plain,
% 1.95/2.21      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.21      inference('sup-', [status(thm)], ['547', '548'])).
% 1.95/2.21  thf('550', plain,
% 1.95/2.21      (![X32 : $i, X33 : $i]:
% 1.95/2.21         (~ (l1_struct_0 @ X32)
% 1.95/2.21          | ~ (l1_struct_0 @ X33)
% 1.95/2.21          | (r1_tsep_1 @ X33 @ X32)
% 1.95/2.21          | ~ (r1_tsep_1 @ X32 @ X33))),
% 1.95/2.21      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.95/2.21  thf('551', plain,
% 1.95/2.21      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 1.95/2.21         | ~ (l1_struct_0 @ sk_B)
% 1.95/2.21         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.21      inference('sup-', [status(thm)], ['549', '550'])).
% 1.95/2.21  thf('552', plain, ((l1_struct_0 @ sk_B)),
% 1.95/2.21      inference('sup-', [status(thm)], ['174', '175'])).
% 1.95/2.21  thf('553', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.21      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.21  thf('554', plain,
% 1.95/2.21      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.21      inference('demod', [status(thm)], ['551', '552', '553'])).
% 1.95/2.21  thf('555', plain,
% 1.95/2.21      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 1.95/2.21      inference('split', [status(esa)], ['0'])).
% 1.95/2.21  thf('556', plain,
% 1.95/2.21      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 1.95/2.21      inference('sup-', [status(thm)], ['554', '555'])).
% 1.95/2.21  thf('557', plain,
% 1.95/2.21      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.95/2.21      inference('sup-', [status(thm)], ['547', '548'])).
% 1.95/2.21  thf('558', plain,
% 1.95/2.21      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 1.95/2.21      inference('split', [status(esa)], ['0'])).
% 1.95/2.21  thf('559', plain,
% 1.95/2.21      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.95/2.21      inference('sup-', [status(thm)], ['557', '558'])).
% 1.95/2.21  thf('560', plain,
% 1.95/2.21      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 1.95/2.21      inference('split', [status(esa)], ['0'])).
% 1.95/2.21  thf('561', plain,
% 1.95/2.21      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 1.95/2.21      inference('split', [status(esa)], ['225'])).
% 1.95/2.21  thf('562', plain, (((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 1.95/2.21      inference('sat_resolution*', [status(thm)], ['556', '559', '560', '561'])).
% 1.95/2.21  thf('563', plain,
% 1.95/2.21      ((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))),
% 1.95/2.21      inference('simpl_trail', [status(thm)], ['531', '562'])).
% 1.95/2.21  thf('564', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 1.95/2.21      inference('demod', [status(thm)], ['222', '563'])).
% 1.95/2.21  thf('565', plain,
% 1.95/2.21      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 1.95/2.21      inference('split', [status(esa)], ['0'])).
% 1.95/2.21  thf('566', plain, (((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.95/2.21      inference('sup-', [status(thm)], ['564', '565'])).
% 1.95/2.21  thf('567', plain,
% 1.95/2.21      (~ ((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.95/2.21      inference('split', [status(esa)], ['0'])).
% 1.95/2.21  thf('568', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 1.95/2.21      inference('sat_resolution*', [status(thm)], ['566', '567'])).
% 1.95/2.21  thf('569', plain, (~ (r1_tsep_1 @ sk_B @ sk_D_2)),
% 1.95/2.21      inference('simpl_trail', [status(thm)], ['1', '568'])).
% 1.95/2.21  thf('570', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 1.95/2.21      inference('demod', [status(thm)], ['222', '563'])).
% 1.95/2.21  thf('571', plain,
% 1.95/2.21      (![X32 : $i, X33 : $i]:
% 1.95/2.21         (~ (l1_struct_0 @ X32)
% 1.95/2.21          | ~ (l1_struct_0 @ X33)
% 1.95/2.21          | (r1_tsep_1 @ X33 @ X32)
% 1.95/2.21          | ~ (r1_tsep_1 @ X32 @ X33))),
% 1.95/2.21      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.95/2.21  thf('572', plain,
% 1.95/2.21      (((r1_tsep_1 @ sk_B @ sk_D_2)
% 1.95/2.21        | ~ (l1_struct_0 @ sk_B)
% 1.95/2.21        | ~ (l1_struct_0 @ sk_D_2))),
% 1.95/2.21      inference('sup-', [status(thm)], ['570', '571'])).
% 1.95/2.21  thf('573', plain, ((l1_struct_0 @ sk_B)),
% 1.95/2.21      inference('sup-', [status(thm)], ['174', '175'])).
% 1.95/2.21  thf('574', plain, ((l1_struct_0 @ sk_D_2)),
% 1.95/2.21      inference('sup-', [status(thm)], ['52', '53'])).
% 1.95/2.21  thf('575', plain, ((r1_tsep_1 @ sk_B @ sk_D_2)),
% 1.95/2.21      inference('demod', [status(thm)], ['572', '573', '574'])).
% 1.95/2.21  thf('576', plain, ($false), inference('demod', [status(thm)], ['569', '575'])).
% 1.95/2.21  
% 1.95/2.21  % SZS output end Refutation
% 1.95/2.21  
% 1.95/2.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
