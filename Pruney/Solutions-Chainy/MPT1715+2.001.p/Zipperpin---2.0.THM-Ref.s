%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nB3wHkrAEL

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:23 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  491 (17887 expanded)
%              Number of leaves         :   40 (4856 expanded)
%              Depth                    :   36
%              Number of atoms          : 3865 (299005 expanded)
%              Number of equality atoms :   62 (1250 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t24_tmap_1,conjecture,(
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
                   => ( ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) )
                      | ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) )).

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
                     => ( ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) )
                        | ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tmap_1])).

thf('2',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('5',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','12','19'])).

thf('21',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['0','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

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

thf('31',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ( m1_pre_topc @ X37 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

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

thf('38',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['45','46'])).

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

thf('48',plain,(
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

thf('49',plain,(
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
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
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
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('52',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('63',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('68',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['60','66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t22_tsep_1,axiom,(
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
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('71',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_pre_topc @ X34 @ ( k1_tsep_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('74',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('86',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('88',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('89',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('91',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('94',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','89','94'])).

thf('96',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('98',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['57','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('101',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

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

thf('106',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('109',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('110',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('114',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('117',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('119',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('122',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('123',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('124',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['104','120','121','124'])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('130',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('135',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('137',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('138',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['131','132'])).

thf('148',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('149',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('151',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('152',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['131','132'])).

thf('154',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('155',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('157',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','152','157'])).

thf('159',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['138','158'])).

thf('160',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('161',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['127','161'])).

thf('163',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('164',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('165',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['131','132'])).

thf('168',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('169',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('171',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('173',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('175',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('177',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('178',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('180',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('181',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['175','181'])).

thf('183',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['166','182'])).

thf('184',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('185',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['126','185'])).

thf('187',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('188',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('189',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('191',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('192',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('194',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('199',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('203',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['200','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['197','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('213',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('216',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('221',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['213','219','220'])).

thf('222',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('223',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('224',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_pre_topc @ X34 @ ( k1_tsep_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('227',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','229'])).

thf('231',plain,
    ( ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['209','210'])).

thf('237',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('238',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('240',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('241',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['209','210'])).

thf('243',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('244',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('246',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['235','241','246'])).

thf('248',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['221','247'])).

thf('249',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('250',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['191','250'])).

thf('252',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('253',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('254',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['251','254'])).

thf('256',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['209','210'])).

thf('257',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('258',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('260',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('262',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('264',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('266',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('267',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('269',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('270',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('271',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['264','270'])).

thf('272',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['255','271'])).

thf('273',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('274',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','274'])).

thf('276',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('277',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['203','204'])).

thf('278',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('279',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['275','276','279'])).

thf('281',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('283',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('284',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['281','287'])).

thf('289',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','125','189','280','292'])).

thf('294',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('298',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('299',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['295','296','297','298'])).

thf('300',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['300','301'])).

thf('303',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['302','303'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('305',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','306'])).

thf('308',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('309',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('310',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('312',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('317',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('318',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['315','321'])).

thf('323',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['323','324'])).

thf('326',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('327',plain,
    ( ~ ( v2_pre_topc @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('330',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    v2_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['330','331','332'])).

thf('334',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('335',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['327','333','334'])).

thf('336',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('337',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('338',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_pre_topc @ X34 @ ( k1_tsep_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('339',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ~ ( v2_pre_topc @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,(
    v2_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['330','331','332'])).

thf('341',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['339','340','341'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['336','343'])).

thf('345',plain,
    ( ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('348',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('349',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['323','324'])).

thf('351',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('352',plain,
    ( ~ ( v2_pre_topc @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,(
    v2_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['330','331','332'])).

thf('354',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('355',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['352','353','354'])).

thf('356',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['323','324'])).

thf('357',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('358',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('360',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['349','355','360'])).

thf('362',plain,
    ( ~ ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['335','361'])).

thf('363',plain,(
    m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('364',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['362','363'])).

thf('365',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['309','364'])).

thf('366',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('367',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('368',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('369',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['365','368'])).

thf('370',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('371',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['369','370'])).

thf('372',plain,(
    m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('373',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('374',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) )
    | ~ ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('375',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('376',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('377',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['374','375','376'])).

thf('378',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('379',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['377','378'])).

thf('380',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['323','324'])).

thf('381',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('382',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['380','381'])).

thf('383',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('384',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['382','383'])).

thf('385',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('386',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['384','385'])).

thf('387',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['379','386'])).

thf('388',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['379','386'])).

thf('389',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['371','387','388'])).

thf('390',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['308','389'])).

thf('391',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('392',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('393',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['390','391','392'])).

thf('394',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['275','276','279'])).

thf('395',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('396',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['277','278'])).

thf('398',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['396','397'])).

thf('399',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['393','398'])).

thf('400',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('401',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['399','400'])).

thf('402',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['307','401'])).

thf('403',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['403'])).

thf('405',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['402','404'])).

thf('406',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('407',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('408',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('409',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('410',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['408','409'])).

thf('411',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('412',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('413',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['410','411','412'])).

thf('414',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('415',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['413','414'])).

thf('416',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('417',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('418',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['415','416','417'])).

thf('419',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['407','418'])).

thf('420',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('421',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['419','420'])).

thf('422',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['406','421'])).

thf('423',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('424',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['422','423'])).

thf('425',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('426',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['424','425'])).

thf('427',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['399','400'])).

thf('428',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['426','427'])).

thf('429',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('430',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['428','429'])).

thf('431',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['277','278'])).

thf('432',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('433',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['430','431','432'])).

thf('434',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['403'])).

thf('435',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['433','434'])).

thf('436',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['307','401'])).

thf('437',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('438',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['436','437'])).

thf('439',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['277','278'])).

thf('440',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('441',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('442',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['403'])).

thf('443',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['441','442'])).

thf('444',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['403'])).

thf('445',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['426','427'])).

thf('446',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['403'])).

thf('447',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['445','446'])).

thf('448',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('449',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['405','435','443','444','447','448'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nB3wHkrAEL
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 1687 iterations in 0.643s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.11  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.90/1.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.11  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.90/1.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.11  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.90/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.90/1.11  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.90/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.11  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.90/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.11  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.90/1.11  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.90/1.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.11  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.90/1.11  thf(d3_struct_0, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.90/1.11  thf('0', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('1', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf(t24_tmap_1, conjecture,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.11           ( ![C:$i]:
% 0.90/1.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.11               ( ![D:$i]:
% 0.90/1.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.11                   ( ( m1_pre_topc @ B @ C ) =>
% 0.90/1.11                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.90/1.11                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.90/1.11                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (~( ![A:$i]:
% 0.90/1.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.11            ( l1_pre_topc @ A ) ) =>
% 0.90/1.11          ( ![B:$i]:
% 0.90/1.11            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.11              ( ![C:$i]:
% 0.90/1.11                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.11                  ( ![D:$i]:
% 0.90/1.11                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.11                      ( ( m1_pre_topc @ B @ C ) =>
% 0.90/1.11                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.90/1.11                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.90/1.11                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.90/1.11  thf('2', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('split', [status(esa)], ['2'])).
% 0.90/1.11  thf(d3_tsep_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( l1_struct_0 @ A ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( l1_struct_0 @ B ) =>
% 0.90/1.11           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.90/1.11             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.90/1.11  thf('4', plain,
% 0.90/1.11      (![X27 : $i, X28 : $i]:
% 0.90/1.11         (~ (l1_struct_0 @ X27)
% 0.90/1.11          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.90/1.11          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.90/1.11          | ~ (l1_struct_0 @ X28))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.90/1.11  thf('5', plain,
% 0.90/1.11      (((~ (l1_struct_0 @ sk_D_2)
% 0.90/1.11         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.90/1.11         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.11  thf('6', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(dt_m1_pre_topc, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( l1_pre_topc @ A ) =>
% 0.90/1.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('8', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.11  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('10', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf(dt_l1_pre_topc, axiom,
% 0.90/1.11    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.90/1.11  thf('11', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('12', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('14', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.11  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('18', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('19', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('20', plain,
% 0.90/1.11      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['5', '12', '19'])).
% 0.90/1.11  thf('21', plain,
% 0.90/1.11      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.90/1.11         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['1', '20'])).
% 0.90/1.11  thf('22', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('23', plain,
% 0.90/1.11      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.11  thf('24', plain,
% 0.90/1.11      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.90/1.11         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['0', '23'])).
% 0.90/1.11  thf('25', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('26', plain,
% 0.90/1.11      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.11  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('28', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(d10_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.11  thf('29', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.11      inference('simplify', [status(thm)], ['29'])).
% 0.90/1.11  thf(t4_tsep_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.11           ( ![C:$i]:
% 0.90/1.11             ( ( m1_pre_topc @ C @ A ) =>
% 0.90/1.11               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.90/1.11                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.90/1.11  thf('31', plain,
% 0.90/1.11      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X37 @ X38)
% 0.90/1.11          | ~ (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.90/1.11          | (m1_pre_topc @ X37 @ X39)
% 0.90/1.11          | ~ (m1_pre_topc @ X39 @ X38)
% 0.90/1.11          | ~ (l1_pre_topc @ X38)
% 0.90/1.11          | ~ (v2_pre_topc @ X38))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.90/1.11  thf('32', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (~ (v2_pre_topc @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | (m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.11  thf('33', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('34', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_A)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.11        | (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['28', '33'])).
% 0.90/1.11  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('37', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf(dt_k1_tsep_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.90/1.11         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.90/1.11         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.11       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.90/1.11         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.90/1.11         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.90/1.11  thf('38', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X29)
% 0.90/1.11          | ~ (l1_pre_topc @ X30)
% 0.90/1.11          | (v2_struct_0 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X31)
% 0.90/1.11          | ~ (m1_pre_topc @ X31 @ X30)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.90/1.11  thf('39', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.11  thf('40', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('41', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['39', '40'])).
% 0.90/1.11  thf('42', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['41'])).
% 0.90/1.11  thf('43', plain,
% 0.90/1.11      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['27', '42'])).
% 0.90/1.11  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('45', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['43', '44'])).
% 0.90/1.11  thf('46', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('47', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['45', '46'])).
% 0.90/1.11  thf(d2_tsep_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.11           ( ![C:$i]:
% 0.90/1.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.11               ( ![D:$i]:
% 0.90/1.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.90/1.11                     ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.11                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.90/1.11                     ( ( u1_struct_0 @ D ) =
% 0.90/1.11                       ( k2_xboole_0 @
% 0.90/1.11                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.11  thf('48', plain,
% 0.90/1.11      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.11         ((v2_struct_0 @ X23)
% 0.90/1.11          | ~ (m1_pre_topc @ X23 @ X24)
% 0.90/1.11          | (v2_struct_0 @ X25)
% 0.90/1.11          | ~ (v1_pre_topc @ X25)
% 0.90/1.11          | ~ (m1_pre_topc @ X25 @ X24)
% 0.90/1.11          | ((X25) != (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.90/1.11          | ((u1_struct_0 @ X25)
% 0.90/1.11              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.90/1.11          | ~ (m1_pre_topc @ X26 @ X24)
% 0.90/1.11          | (v2_struct_0 @ X26)
% 0.90/1.11          | ~ (l1_pre_topc @ X24)
% 0.90/1.11          | (v2_struct_0 @ X24))),
% 0.90/1.11      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.90/1.11  thf('49', plain,
% 0.90/1.11      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.90/1.11         ((v2_struct_0 @ X24)
% 0.90/1.11          | ~ (l1_pre_topc @ X24)
% 0.90/1.11          | (v2_struct_0 @ X26)
% 0.90/1.11          | ~ (m1_pre_topc @ X26 @ X24)
% 0.90/1.11          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.90/1.11              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.90/1.11          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 0.90/1.11          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.90/1.11          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.90/1.11          | ~ (m1_pre_topc @ X23 @ X24)
% 0.90/1.11          | (v2_struct_0 @ X23))),
% 0.90/1.11      inference('simplify', [status(thm)], ['48'])).
% 0.90/1.11  thf('50', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.90/1.11        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['47', '49'])).
% 0.90/1.11  thf('51', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf('52', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('53', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('54', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.11  thf('55', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_B)
% 0.90/1.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.90/1.11        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.90/1.11  thf('56', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('57', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('58', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['45', '46'])).
% 0.90/1.11  thf('59', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('60', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_C_1)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ 
% 0.90/1.11           (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.11  thf('61', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(cc1_pre_topc, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.90/1.11  thf('62', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('63', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_A)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.11        | (v2_pre_topc @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.11  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('66', plain, ((v2_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('67', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('68', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ 
% 0.90/1.11        (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['60', '66', '67'])).
% 0.90/1.11  thf('69', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('70', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf(t22_tsep_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.11           ( ![C:$i]:
% 0.90/1.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.11               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.90/1.11  thf('71', plain,
% 0.90/1.11      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.11         ((v2_struct_0 @ X34)
% 0.90/1.11          | ~ (m1_pre_topc @ X34 @ X35)
% 0.90/1.11          | (m1_pre_topc @ X34 @ (k1_tsep_1 @ X35 @ X34 @ X36))
% 0.90/1.11          | ~ (m1_pre_topc @ X36 @ X35)
% 0.90/1.11          | (v2_struct_0 @ X36)
% 0.90/1.11          | ~ (l1_pre_topc @ X35)
% 0.90/1.11          | ~ (v2_pre_topc @ X35)
% 0.90/1.11          | (v2_struct_0 @ X35))),
% 0.90/1.11      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.90/1.11  thf('72', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_C_1)
% 0.90/1.11          | ~ (v2_pre_topc @ sk_C_1)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['70', '71'])).
% 0.90/1.11  thf('73', plain, ((v2_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('74', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('75', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.90/1.11  thf('76', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['75'])).
% 0.90/1.11  thf('77', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['69', '76'])).
% 0.90/1.11  thf('78', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('79', plain,
% 0.90/1.11      (((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['77', '78'])).
% 0.90/1.11  thf('80', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('81', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['79', '80'])).
% 0.90/1.11  thf('82', plain,
% 0.90/1.11      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X37 @ X38)
% 0.90/1.11          | ~ (m1_pre_topc @ X37 @ X39)
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.90/1.11          | ~ (m1_pre_topc @ X39 @ X38)
% 0.90/1.11          | ~ (l1_pre_topc @ X38)
% 0.90/1.11          | ~ (v2_pre_topc @ X38))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.90/1.11  thf('83', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.11  thf('84', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['45', '46'])).
% 0.90/1.11  thf('85', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('86', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_C_1)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['84', '85'])).
% 0.90/1.11  thf('87', plain, ((v2_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('88', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('89', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.90/1.11  thf('90', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['45', '46'])).
% 0.90/1.11  thf('91', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('92', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.11  thf('93', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('94', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['92', '93'])).
% 0.90/1.11  thf('95', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['83', '89', '94'])).
% 0.90/1.11  thf('96', plain,
% 0.90/1.11      ((~ (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.90/1.11           (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['68', '95'])).
% 0.90/1.11  thf('97', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['79', '80'])).
% 0.90/1.11  thf('98', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.90/1.11        (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['96', '97'])).
% 0.90/1.11  thf('99', plain,
% 0.90/1.11      (((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11         (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))
% 0.90/1.11        | ~ (l1_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['57', '98'])).
% 0.90/1.11  thf('100', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('101', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11        (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['99', '100'])).
% 0.90/1.11  thf('102', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('103', plain,
% 0.90/1.11      ((~ (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11            = (k2_struct_0 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.11  thf('104', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11            = (k2_struct_0 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['56', '103'])).
% 0.90/1.11  thf('105', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['79', '80'])).
% 0.90/1.11  thf(d9_pre_topc, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( l1_pre_topc @ A ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( l1_pre_topc @ B ) =>
% 0.90/1.11           ( ( m1_pre_topc @ B @ A ) <=>
% 0.90/1.11             ( ( ![C:$i]:
% 0.90/1.11                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.90/1.11                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.90/1.11                     ( ?[D:$i]:
% 0.90/1.11                       ( ( m1_subset_1 @
% 0.90/1.11                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.90/1.11                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.90/1.11                         ( ( C ) =
% 0.90/1.11                           ( k9_subset_1 @
% 0.90/1.11                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.90/1.11               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.90/1.11  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.90/1.11  thf(zf_stmt_2, axiom,
% 0.90/1.11    (![D:$i,C:$i,B:$i,A:$i]:
% 0.90/1.11     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.90/1.11       ( ( ( C ) =
% 0.90/1.11           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.90/1.11         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.90/1.11         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.11  thf(zf_stmt_3, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( l1_pre_topc @ A ) =>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ( l1_pre_topc @ B ) =>
% 0.90/1.11           ( ( m1_pre_topc @ B @ A ) <=>
% 0.90/1.11             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.90/1.11               ( ![C:$i]:
% 0.90/1.11                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.90/1.11                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.90/1.11                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.11  thf('106', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('107', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.11  thf('108', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['92', '93'])).
% 0.90/1.11  thf('109', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('110', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.90/1.11  thf('111', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('112', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11            = (k2_struct_0 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['110', '111'])).
% 0.90/1.11  thf('113', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['45', '46'])).
% 0.90/1.11  thf('114', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('115', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['113', '114'])).
% 0.90/1.11  thf('116', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('117', plain,
% 0.90/1.11      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.90/1.11         (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['115', '116'])).
% 0.90/1.11  thf('118', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['92', '93'])).
% 0.90/1.11  thf('119', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.90/1.11        (k2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['117', '118'])).
% 0.90/1.11  thf('120', plain,
% 0.90/1.11      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11         = (k2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['112', '119'])).
% 0.90/1.11  thf('121', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.11      inference('simplify', [status(thm)], ['29'])).
% 0.90/1.11  thf('122', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['92', '93'])).
% 0.90/1.11  thf('123', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('124', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['122', '123'])).
% 0.90/1.11  thf('125', plain,
% 0.90/1.11      (((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11         = (k2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['104', '120', '121', '124'])).
% 0.90/1.11  thf('126', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('127', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('128', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf('129', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['41'])).
% 0.90/1.11  thf('130', plain,
% 0.90/1.11      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['128', '129'])).
% 0.90/1.11  thf('131', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['130'])).
% 0.90/1.11  thf('132', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('133', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['131', '132'])).
% 0.90/1.11  thf('134', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('135', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_C_1)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ 
% 0.90/1.11           (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['133', '134'])).
% 0.90/1.11  thf('136', plain, ((v2_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('137', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('138', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ 
% 0.90/1.11        (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.90/1.11  thf('139', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf('140', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['75'])).
% 0.90/1.11  thf('141', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['139', '140'])).
% 0.90/1.11  thf('142', plain,
% 0.90/1.11      (((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['141'])).
% 0.90/1.11  thf('143', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('144', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['142', '143'])).
% 0.90/1.11  thf('145', plain,
% 0.90/1.11      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X37 @ X38)
% 0.90/1.11          | ~ (m1_pre_topc @ X37 @ X39)
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.90/1.11          | ~ (m1_pre_topc @ X39 @ X38)
% 0.90/1.11          | ~ (l1_pre_topc @ X38)
% 0.90/1.11          | ~ (v2_pre_topc @ X38))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.90/1.11  thf('146', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['144', '145'])).
% 0.90/1.11  thf('147', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['131', '132'])).
% 0.90/1.11  thf('148', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('149', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_C_1)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['147', '148'])).
% 0.90/1.11  thf('150', plain, ((v2_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('151', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('152', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.90/1.11  thf('153', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['131', '132'])).
% 0.90/1.11  thf('154', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('155', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['153', '154'])).
% 0.90/1.11  thf('156', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('157', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['155', '156'])).
% 0.90/1.11  thf('158', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['146', '152', '157'])).
% 0.90/1.11  thf('159', plain,
% 0.90/1.11      ((~ (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.90/1.11           (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['138', '158'])).
% 0.90/1.11  thf('160', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['142', '143'])).
% 0.90/1.11  thf('161', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.90/1.11        (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['159', '160'])).
% 0.90/1.11  thf('162', plain,
% 0.90/1.11      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.90/1.11         (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.90/1.11        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['127', '161'])).
% 0.90/1.11  thf('163', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['155', '156'])).
% 0.90/1.11  thf('164', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('165', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['163', '164'])).
% 0.90/1.11  thf('166', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['162', '165'])).
% 0.90/1.11  thf('167', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['131', '132'])).
% 0.90/1.11  thf('168', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('169', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (r1_tarski @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['167', '168'])).
% 0.90/1.11  thf('170', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('171', plain,
% 0.90/1.11      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 0.90/1.11         (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['169', '170'])).
% 0.90/1.11  thf('172', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['155', '156'])).
% 0.90/1.11  thf('173', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 0.90/1.11        (k2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['171', '172'])).
% 0.90/1.11  thf('174', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('175', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1)
% 0.90/1.11            = (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['173', '174'])).
% 0.90/1.11  thf('176', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['142', '143'])).
% 0.90/1.11  thf('177', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('178', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.90/1.11        | (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['176', '177'])).
% 0.90/1.11  thf('179', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['155', '156'])).
% 0.90/1.11  thf('180', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('181', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.90/1.11  thf('182', plain,
% 0.90/1.11      (((k2_struct_0 @ sk_C_1)
% 0.90/1.11         = (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['175', '181'])).
% 0.90/1.11  thf('183', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['166', '182'])).
% 0.90/1.11  thf('184', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('185', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['183', '184'])).
% 0.90/1.11  thf('186', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 0.90/1.11        | ~ (l1_struct_0 @ sk_C_1)
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['126', '185'])).
% 0.90/1.11  thf('187', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.11      inference('simplify', [status(thm)], ['29'])).
% 0.90/1.11  thf('188', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('189', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.90/1.11  thf('190', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('191', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('192', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('193', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('194', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_A)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.11        | (m1_pre_topc @ sk_B @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['192', '193'])).
% 0.90/1.11  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('197', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.90/1.11  thf('198', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.90/1.11  thf('199', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X29)
% 0.90/1.11          | ~ (l1_pre_topc @ X30)
% 0.90/1.11          | (v2_struct_0 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X31)
% 0.90/1.11          | ~ (m1_pre_topc @ X31 @ X30)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.90/1.11  thf('200', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_B)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['198', '199'])).
% 0.90/1.11  thf('201', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('202', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('203', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['201', '202'])).
% 0.90/1.11  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('205', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('206', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['200', '205'])).
% 0.90/1.11  thf('207', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B))),
% 0.90/1.11      inference('simplify', [status(thm)], ['206'])).
% 0.90/1.11  thf('208', plain,
% 0.90/1.11      (((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['197', '207'])).
% 0.90/1.11  thf('209', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_B)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B))),
% 0.90/1.11      inference('simplify', [status(thm)], ['208'])).
% 0.90/1.11  thf('210', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('211', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.90/1.11      inference('clc', [status(thm)], ['209', '210'])).
% 0.90/1.11  thf('212', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('213', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_B)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_B)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ 
% 0.90/1.11           (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['211', '212'])).
% 0.90/1.11  thf('214', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('215', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('216', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['214', '215'])).
% 0.90/1.11  thf('217', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('219', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.90/1.11  thf('220', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('221', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ 
% 0.90/1.11        (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['213', '219', '220'])).
% 0.90/1.11  thf('222', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.90/1.11  thf('223', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.90/1.11  thf('224', plain,
% 0.90/1.11      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.11         ((v2_struct_0 @ X34)
% 0.90/1.11          | ~ (m1_pre_topc @ X34 @ X35)
% 0.90/1.11          | (m1_pre_topc @ X34 @ (k1_tsep_1 @ X35 @ X34 @ X36))
% 0.90/1.11          | ~ (m1_pre_topc @ X36 @ X35)
% 0.90/1.11          | (v2_struct_0 @ X36)
% 0.90/1.11          | ~ (l1_pre_topc @ X35)
% 0.90/1.11          | ~ (v2_pre_topc @ X35)
% 0.90/1.11          | (v2_struct_0 @ X35))),
% 0.90/1.11      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.90/1.11  thf('225', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_B)
% 0.90/1.11          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.11          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 0.90/1.11          | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['223', '224'])).
% 0.90/1.11  thf('226', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.90/1.11  thf('227', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('228', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.11          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 0.90/1.11          | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.90/1.11  thf('229', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('simplify', [status(thm)], ['228'])).
% 0.90/1.11  thf('230', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['222', '229'])).
% 0.90/1.11  thf('231', plain,
% 0.90/1.11      (((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11        | (v2_struct_0 @ sk_B))),
% 0.90/1.11      inference('simplify', [status(thm)], ['230'])).
% 0.90/1.11  thf('232', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('233', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['231', '232'])).
% 0.90/1.11  thf('234', plain,
% 0.90/1.11      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X37 @ X38)
% 0.90/1.11          | ~ (m1_pre_topc @ X37 @ X39)
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.90/1.11          | ~ (m1_pre_topc @ X39 @ X38)
% 0.90/1.11          | ~ (l1_pre_topc @ X38)
% 0.90/1.11          | ~ (v2_pre_topc @ X38))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.90/1.11  thf('235', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['233', '234'])).
% 0.90/1.11  thf('236', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.90/1.11      inference('clc', [status(thm)], ['209', '210'])).
% 0.90/1.11  thf('237', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('238', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_B)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_B)
% 0.90/1.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['236', '237'])).
% 0.90/1.11  thf('239', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.90/1.11  thf('240', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('241', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.90/1.11  thf('242', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.90/1.11      inference('clc', [status(thm)], ['209', '210'])).
% 0.90/1.11  thf('243', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('244', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['242', '243'])).
% 0.90/1.11  thf('245', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('246', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['244', '245'])).
% 0.90/1.11  thf('247', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['235', '241', '246'])).
% 0.90/1.11  thf('248', plain,
% 0.90/1.11      ((~ (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11        | (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.11           (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['221', '247'])).
% 0.90/1.11  thf('249', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['231', '232'])).
% 0.90/1.11  thf('250', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.11        (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['248', '249'])).
% 0.90/1.11  thf('251', plain,
% 0.90/1.11      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.11         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 0.90/1.11        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['191', '250'])).
% 0.90/1.11  thf('252', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['244', '245'])).
% 0.90/1.11  thf('253', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('254', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['252', '253'])).
% 0.90/1.11  thf('255', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['251', '254'])).
% 0.90/1.11  thf('256', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.90/1.11      inference('clc', [status(thm)], ['209', '210'])).
% 0.90/1.11  thf('257', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('258', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.11        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_B))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['256', '257'])).
% 0.90/1.11  thf('259', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('260', plain,
% 0.90/1.11      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 0.90/1.11         (k2_struct_0 @ sk_B))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['258', '259'])).
% 0.90/1.11  thf('261', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['244', '245'])).
% 0.90/1.11  thf('262', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 0.90/1.11        (k2_struct_0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['260', '261'])).
% 0.90/1.11  thf('263', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('264', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 0.90/1.11        | ((k2_struct_0 @ sk_B)
% 0.90/1.11            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['262', '263'])).
% 0.90/1.11  thf('265', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['231', '232'])).
% 0.90/1.11  thf('266', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('267', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.90/1.11        | (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 0.90/1.11        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['265', '266'])).
% 0.90/1.11  thf('268', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['244', '245'])).
% 0.90/1.11  thf('269', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('270', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['267', '268', '269'])).
% 0.90/1.11  thf('271', plain,
% 0.90/1.11      (((k2_struct_0 @ sk_B) = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.90/1.11      inference('demod', [status(thm)], ['264', '270'])).
% 0.90/1.11  thf('272', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['255', '271'])).
% 0.90/1.11  thf('273', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('274', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.90/1.11        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['272', '273'])).
% 0.90/1.11  thf('275', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.90/1.11        | ~ (l1_struct_0 @ sk_B)
% 0.90/1.11        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['190', '274'])).
% 0.90/1.11  thf('276', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.11      inference('simplify', [status(thm)], ['29'])).
% 0.90/1.11  thf('277', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.11      inference('demod', [status(thm)], ['203', '204'])).
% 0.90/1.11  thf('278', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('279', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.11      inference('sup-', [status(thm)], ['277', '278'])).
% 0.90/1.11  thf('280', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['275', '276', '279'])).
% 0.90/1.11  thf('281', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('282', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf('283', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X29)
% 0.90/1.11          | ~ (l1_pre_topc @ X30)
% 0.90/1.11          | (v2_struct_0 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X31)
% 0.90/1.11          | ~ (m1_pre_topc @ X31 @ X30)
% 0.90/1.11          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.90/1.11  thf('284', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['282', '283'])).
% 0.90/1.11  thf('285', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('286', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['284', '285'])).
% 0.90/1.11  thf('287', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_C_1)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.90/1.11          | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0)))),
% 0.90/1.11      inference('simplify', [status(thm)], ['286'])).
% 0.90/1.11  thf('288', plain,
% 0.90/1.11      (((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['281', '287'])).
% 0.90/1.11  thf('289', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('290', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.90/1.11      inference('clc', [status(thm)], ['288', '289'])).
% 0.90/1.11  thf('291', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('292', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.90/1.11      inference('clc', [status(thm)], ['290', '291'])).
% 0.90/1.11  thf('293', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_B)
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1)
% 0.90/1.11            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.90/1.11        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['55', '125', '189', '280', '292'])).
% 0.90/1.11  thf('294', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X29)
% 0.90/1.11          | ~ (l1_pre_topc @ X30)
% 0.90/1.11          | (v2_struct_0 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X31)
% 0.90/1.11          | ~ (m1_pre_topc @ X31 @ X30)
% 0.90/1.11          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.90/1.11  thf('295', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1)
% 0.90/1.11            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1)
% 0.90/1.11        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['293', '294'])).
% 0.90/1.11  thf('296', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('297', plain, ((l1_pre_topc @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.11  thf('298', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf('299', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1)
% 0.90/1.11            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_B)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1)
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['295', '296', '297', '298'])).
% 0.90/1.11  thf('300', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_B)
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1)
% 0.90/1.11            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.90/1.11        | (v2_struct_0 @ sk_C_1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['299'])).
% 0.90/1.11  thf('301', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('302', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_C_1)
% 0.90/1.11        | ((k2_struct_0 @ sk_C_1)
% 0.90/1.11            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))))),
% 0.90/1.11      inference('clc', [status(thm)], ['300', '301'])).
% 0.90/1.11  thf('303', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('304', plain,
% 0.90/1.11      (((k2_struct_0 @ sk_C_1)
% 0.90/1.11         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 0.90/1.11      inference('clc', [status(thm)], ['302', '303'])).
% 0.90/1.11  thf(t70_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.90/1.11            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.90/1.11       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.90/1.11            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.90/1.11  thf('305', plain,
% 0.90/1.11      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.90/1.11         ((r1_xboole_0 @ X3 @ X6)
% 0.90/1.11          | ~ (r1_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X6)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.90/1.11  thf('306', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.90/1.11          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['304', '305'])).
% 0.90/1.11  thf('307', plain,
% 0.90/1.11      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['26', '306'])).
% 0.90/1.11  thf('308', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('309', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('310', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('311', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('312', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_A)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.11        | (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['310', '311'])).
% 0.90/1.11  thf('313', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('314', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('315', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['312', '313', '314'])).
% 0.90/1.11  thf('316', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['312', '313', '314'])).
% 0.90/1.11  thf('317', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X29)
% 0.90/1.11          | ~ (l1_pre_topc @ X30)
% 0.90/1.11          | (v2_struct_0 @ X30)
% 0.90/1.11          | (v2_struct_0 @ X31)
% 0.90/1.11          | ~ (m1_pre_topc @ X31 @ X30)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.90/1.11  thf('318', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_D_2)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['316', '317'])).
% 0.90/1.11  thf('319', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('320', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['318', '319'])).
% 0.90/1.11  thf('321', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.90/1.11          | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2))),
% 0.90/1.11      inference('simplify', [status(thm)], ['320'])).
% 0.90/1.11  thf('322', plain,
% 0.90/1.11      (((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 0.90/1.11        | (v2_struct_0 @ sk_D_2)
% 0.90/1.11        | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['315', '321'])).
% 0.90/1.11  thf('323', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_D_2)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2))),
% 0.90/1.11      inference('simplify', [status(thm)], ['322'])).
% 0.90/1.11  thf('324', plain, (~ (v2_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('325', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.90/1.11      inference('clc', [status(thm)], ['323', '324'])).
% 0.90/1.11  thf('326', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((m1_pre_topc @ X0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ X1)
% 0.90/1.11          | ~ (l1_pre_topc @ X1)
% 0.90/1.11          | ~ (v2_pre_topc @ X1))),
% 0.90/1.11      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.11  thf('327', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_D_2)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_D_2)
% 0.90/1.11        | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ 
% 0.90/1.11           (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['325', '326'])).
% 0.90/1.11  thf('328', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('329', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('330', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_A)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.11        | (v2_pre_topc @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['328', '329'])).
% 0.90/1.11  thf('331', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('332', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('333', plain, ((v2_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['330', '331', '332'])).
% 0.90/1.11  thf('334', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('335', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ 
% 0.90/1.11        (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['327', '333', '334'])).
% 0.90/1.11  thf('336', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['312', '313', '314'])).
% 0.90/1.11  thf('337', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['312', '313', '314'])).
% 0.90/1.11  thf('338', plain,
% 0.90/1.11      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.11         ((v2_struct_0 @ X34)
% 0.90/1.11          | ~ (m1_pre_topc @ X34 @ X35)
% 0.90/1.11          | (m1_pre_topc @ X34 @ (k1_tsep_1 @ X35 @ X34 @ X36))
% 0.90/1.11          | ~ (m1_pre_topc @ X36 @ X35)
% 0.90/1.11          | (v2_struct_0 @ X36)
% 0.90/1.11          | ~ (l1_pre_topc @ X35)
% 0.90/1.11          | ~ (v2_pre_topc @ X35)
% 0.90/1.11          | (v2_struct_0 @ X35))),
% 0.90/1.11      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.90/1.11  thf('339', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_D_2)
% 0.90/1.11          | ~ (v2_pre_topc @ sk_D_2)
% 0.90/1.11          | ~ (l1_pre_topc @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.90/1.11          | (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 0.90/1.11          | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['337', '338'])).
% 0.90/1.11  thf('340', plain, ((v2_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['330', '331', '332'])).
% 0.90/1.11  thf('341', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('342', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((v2_struct_0 @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.90/1.11          | (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 0.90/1.11          | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['339', '340', '341'])).
% 0.90/1.11  thf('343', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.90/1.11          | (v2_struct_0 @ X0)
% 0.90/1.11          | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('simplify', [status(thm)], ['342'])).
% 0.90/1.11  thf('344', plain,
% 0.90/1.11      (((v2_struct_0 @ sk_D_2)
% 0.90/1.11        | (v2_struct_0 @ sk_D_2)
% 0.90/1.11        | (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['336', '343'])).
% 0.90/1.11  thf('345', plain,
% 0.90/1.11      (((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11        | (v2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('simplify', [status(thm)], ['344'])).
% 0.90/1.11  thf('346', plain, (~ (v2_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('347', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('clc', [status(thm)], ['345', '346'])).
% 0.90/1.11  thf('348', plain,
% 0.90/1.11      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X37 @ X38)
% 0.90/1.11          | ~ (m1_pre_topc @ X37 @ X39)
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.90/1.11          | ~ (m1_pre_topc @ X39 @ X38)
% 0.90/1.11          | ~ (l1_pre_topc @ X38)
% 0.90/1.11          | ~ (v2_pre_topc @ X38))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.90/1.11  thf('349', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_D_2 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['347', '348'])).
% 0.90/1.11  thf('350', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.90/1.11      inference('clc', [status(thm)], ['323', '324'])).
% 0.90/1.11  thf('351', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X7 @ X8)
% 0.90/1.11          | (v2_pre_topc @ X7)
% 0.90/1.11          | ~ (l1_pre_topc @ X8)
% 0.90/1.11          | ~ (v2_pre_topc @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.11  thf('352', plain,
% 0.90/1.11      ((~ (v2_pre_topc @ sk_D_2)
% 0.90/1.11        | ~ (l1_pre_topc @ sk_D_2)
% 0.90/1.11        | (v2_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['350', '351'])).
% 0.90/1.11  thf('353', plain, ((v2_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['330', '331', '332'])).
% 0.90/1.11  thf('354', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('355', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['352', '353', '354'])).
% 0.90/1.11  thf('356', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.90/1.11      inference('clc', [status(thm)], ['323', '324'])).
% 0.90/1.11  thf('357', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.11          | (l1_pre_topc @ X21)
% 0.90/1.11          | ~ (l1_pre_topc @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.11  thf('358', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_D_2)
% 0.90/1.11        | (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['356', '357'])).
% 0.90/1.11  thf('359', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('360', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['358', '359'])).
% 0.90/1.11  thf('361', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11          | (r1_tarski @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ X0))
% 0.90/1.11          | ~ (m1_pre_topc @ sk_D_2 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['349', '355', '360'])).
% 0.90/1.11  thf('362', plain,
% 0.90/1.11      ((~ (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11        | (r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.90/1.11           (u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['335', '361'])).
% 0.90/1.11  thf('363', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('clc', [status(thm)], ['345', '346'])).
% 0.90/1.11  thf('364', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.90/1.11        (u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['362', '363'])).
% 0.90/1.11  thf('365', plain,
% 0.90/1.11      (((r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.90/1.11         (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))
% 0.90/1.11        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['309', '364'])).
% 0.90/1.11  thf('366', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['358', '359'])).
% 0.90/1.11  thf('367', plain,
% 0.90/1.11      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.11  thf('368', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['366', '367'])).
% 0.90/1.11  thf('369', plain,
% 0.90/1.11      ((r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['365', '368'])).
% 0.90/1.11  thf('370', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('371', plain,
% 0.90/1.11      ((~ (r1_tarski @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.90/1.11           (u1_struct_0 @ sk_D_2))
% 0.90/1.11        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11            = (u1_struct_0 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['369', '370'])).
% 0.90/1.11  thf('372', plain,
% 0.90/1.11      ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('clc', [status(thm)], ['345', '346'])).
% 0.90/1.11  thf('373', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('374', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11        | (r1_tarski @ (k2_struct_0 @ sk_D_2) @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))
% 0.90/1.11        | ~ (l1_pre_topc @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['372', '373'])).
% 0.90/1.11  thf('375', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['358', '359'])).
% 0.90/1.11  thf('376', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('377', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ sk_D_2) @ 
% 0.90/1.11        (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['374', '375', '376'])).
% 0.90/1.11  thf('378', plain,
% 0.90/1.11      (![X0 : $i, X2 : $i]:
% 0.90/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('379', plain,
% 0.90/1.11      ((~ (r1_tarski @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_D_2))
% 0.90/1.11        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11            = (k2_struct_0 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['377', '378'])).
% 0.90/1.11  thf('380', plain,
% 0.90/1.11      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.90/1.11      inference('clc', [status(thm)], ['323', '324'])).
% 0.90/1.11  thf('381', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i]:
% 0.90/1.11         (~ (l1_pre_topc @ X15)
% 0.90/1.11          | ~ (m1_pre_topc @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.90/1.11          | ~ (l1_pre_topc @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.11  thf('382', plain,
% 0.90/1.11      ((~ (l1_pre_topc @ sk_D_2)
% 0.90/1.11        | (r1_tarski @ 
% 0.90/1.11           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.90/1.11           (k2_struct_0 @ sk_D_2))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['380', '381'])).
% 0.90/1.11  thf('383', plain, ((l1_pre_topc @ sk_D_2)),
% 0.90/1.11      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.11  thf('384', plain,
% 0.90/1.11      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.90/1.11         (k2_struct_0 @ sk_D_2))
% 0.90/1.11        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['382', '383'])).
% 0.90/1.11  thf('385', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['358', '359'])).
% 0.90/1.11  thf('386', plain,
% 0.90/1.11      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.90/1.11        (k2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['384', '385'])).
% 0.90/1.11  thf('387', plain,
% 0.90/1.11      (((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11         = (k2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['379', '386'])).
% 0.90/1.11  thf('388', plain,
% 0.90/1.11      (((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.90/1.11         = (k2_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['379', '386'])).
% 0.90/1.11  thf('389', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 0.90/1.11        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['371', '387', '388'])).
% 0.90/1.11  thf('390', plain,
% 0.90/1.11      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 0.90/1.11        | ~ (l1_struct_0 @ sk_D_2)
% 0.90/1.11        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['308', '389'])).
% 0.90/1.11  thf('391', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.11      inference('simplify', [status(thm)], ['29'])).
% 0.90/1.11  thf('392', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('393', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('demod', [status(thm)], ['390', '391', '392'])).
% 0.90/1.11  thf('394', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['275', '276', '279'])).
% 0.90/1.11  thf('395', plain,
% 0.90/1.11      (![X27 : $i, X28 : $i]:
% 0.90/1.11         (~ (l1_struct_0 @ X27)
% 0.90/1.11          | ~ (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.90/1.11          | (r1_tsep_1 @ X28 @ X27)
% 0.90/1.11          | ~ (l1_struct_0 @ X28))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.90/1.11  thf('396', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 0.90/1.11          | ~ (l1_struct_0 @ X0)
% 0.90/1.11          | (r1_tsep_1 @ X0 @ sk_B)
% 0.90/1.11          | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['394', '395'])).
% 0.90/1.11  thf('397', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.11      inference('sup-', [status(thm)], ['277', '278'])).
% 0.90/1.11  thf('398', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 0.90/1.11          | ~ (l1_struct_0 @ X0)
% 0.90/1.11          | (r1_tsep_1 @ X0 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['396', '397'])).
% 0.90/1.11  thf('399', plain,
% 0.90/1.11      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 0.90/1.11        | (r1_tsep_1 @ sk_D_2 @ sk_B)
% 0.90/1.11        | ~ (l1_struct_0 @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['393', '398'])).
% 0.90/1.11  thf('400', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('401', plain,
% 0.90/1.11      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 0.90/1.11        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['399', '400'])).
% 0.90/1.11  thf('402', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['307', '401'])).
% 0.90/1.11  thf('403', plain,
% 0.90/1.11      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('404', plain,
% 0.90/1.11      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.90/1.11      inference('split', [status(esa)], ['403'])).
% 0.90/1.11  thf('405', plain,
% 0.90/1.11      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['402', '404'])).
% 0.90/1.11  thf('406', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('407', plain,
% 0.90/1.11      (![X9 : $i]:
% 0.90/1.11         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.11  thf('408', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('split', [status(esa)], ['2'])).
% 0.90/1.11  thf(symmetry_r1_tsep_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.90/1.11       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.90/1.11  thf('409', plain,
% 0.90/1.11      (![X32 : $i, X33 : $i]:
% 0.90/1.11         (~ (l1_struct_0 @ X32)
% 0.90/1.11          | ~ (l1_struct_0 @ X33)
% 0.90/1.11          | (r1_tsep_1 @ X33 @ X32)
% 0.90/1.11          | ~ (r1_tsep_1 @ X32 @ X33))),
% 0.90/1.11      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.90/1.11  thf('410', plain,
% 0.90/1.11      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.90/1.11         | ~ (l1_struct_0 @ sk_D_2)
% 0.90/1.11         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['408', '409'])).
% 0.90/1.11  thf('411', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('412', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('413', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['410', '411', '412'])).
% 0.90/1.11  thf('414', plain,
% 0.90/1.11      (![X27 : $i, X28 : $i]:
% 0.90/1.11         (~ (l1_struct_0 @ X27)
% 0.90/1.11          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.90/1.11          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.90/1.11          | ~ (l1_struct_0 @ X28))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.90/1.11  thf('415', plain,
% 0.90/1.11      (((~ (l1_struct_0 @ sk_D_2)
% 0.90/1.11         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.90/1.11         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['413', '414'])).
% 0.90/1.11  thf('416', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('417', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('418', plain,
% 0.90/1.11      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['415', '416', '417'])).
% 0.90/1.11  thf('419', plain,
% 0.90/1.11      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.90/1.11         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['407', '418'])).
% 0.90/1.11  thf('420', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('421', plain,
% 0.90/1.11      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['419', '420'])).
% 0.90/1.11  thf('422', plain,
% 0.90/1.11      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.90/1.11         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['406', '421'])).
% 0.90/1.11  thf('423', plain, ((l1_struct_0 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf('424', plain,
% 0.90/1.11      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['422', '423'])).
% 0.90/1.11  thf('425', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.90/1.11          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['304', '305'])).
% 0.90/1.11  thf('426', plain,
% 0.90/1.11      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.90/1.11         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['424', '425'])).
% 0.90/1.11  thf('427', plain,
% 0.90/1.11      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 0.90/1.11        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['399', '400'])).
% 0.90/1.11  thf('428', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['426', '427'])).
% 0.90/1.11  thf('429', plain,
% 0.90/1.11      (![X32 : $i, X33 : $i]:
% 0.90/1.11         (~ (l1_struct_0 @ X32)
% 0.90/1.11          | ~ (l1_struct_0 @ X33)
% 0.90/1.11          | (r1_tsep_1 @ X33 @ X32)
% 0.90/1.11          | ~ (r1_tsep_1 @ X32 @ X33))),
% 0.90/1.11      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.90/1.11  thf('430', plain,
% 0.90/1.11      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.90/1.11         | ~ (l1_struct_0 @ sk_B)
% 0.90/1.11         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['428', '429'])).
% 0.90/1.11  thf('431', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.11      inference('sup-', [status(thm)], ['277', '278'])).
% 0.90/1.11  thf('432', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('433', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('demod', [status(thm)], ['430', '431', '432'])).
% 0.90/1.11  thf('434', plain,
% 0.90/1.11      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.90/1.11      inference('split', [status(esa)], ['403'])).
% 0.90/1.11  thf('435', plain,
% 0.90/1.11      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['433', '434'])).
% 0.90/1.11  thf('436', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['307', '401'])).
% 0.90/1.11  thf('437', plain,
% 0.90/1.11      (![X32 : $i, X33 : $i]:
% 0.90/1.11         (~ (l1_struct_0 @ X32)
% 0.90/1.11          | ~ (l1_struct_0 @ X33)
% 0.90/1.11          | (r1_tsep_1 @ X33 @ X32)
% 0.90/1.11          | ~ (r1_tsep_1 @ X32 @ X33))),
% 0.90/1.11      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.90/1.11  thf('438', plain,
% 0.90/1.11      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.90/1.11         | ~ (l1_struct_0 @ sk_B)
% 0.90/1.11         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['436', '437'])).
% 0.90/1.11  thf('439', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.11      inference('sup-', [status(thm)], ['277', '278'])).
% 0.90/1.11  thf('440', plain, ((l1_struct_0 @ sk_D_2)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('441', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['438', '439', '440'])).
% 0.90/1.11  thf('442', plain,
% 0.90/1.11      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.90/1.11      inference('split', [status(esa)], ['403'])).
% 0.90/1.11  thf('443', plain,
% 0.90/1.11      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.90/1.11      inference('sup-', [status(thm)], ['441', '442'])).
% 0.90/1.11  thf('444', plain,
% 0.90/1.11      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.90/1.11      inference('split', [status(esa)], ['403'])).
% 0.90/1.11  thf('445', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['426', '427'])).
% 0.90/1.11  thf('446', plain,
% 0.90/1.11      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.90/1.11      inference('split', [status(esa)], ['403'])).
% 0.90/1.11  thf('447', plain,
% 0.90/1.11      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.90/1.11      inference('sup-', [status(thm)], ['445', '446'])).
% 0.90/1.11  thf('448', plain,
% 0.90/1.11      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.90/1.11      inference('split', [status(esa)], ['2'])).
% 0.90/1.11  thf('449', plain, ($false),
% 0.90/1.11      inference('sat_resolution*', [status(thm)],
% 0.90/1.11                ['405', '435', '443', '444', '447', '448'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
