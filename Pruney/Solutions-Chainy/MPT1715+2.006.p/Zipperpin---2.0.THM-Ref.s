%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bSVHbz7jGF

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:24 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  491 (25675 expanded)
%              Number of leaves         :   39 (6908 expanded)
%              Depth                    :   52
%              Number of atoms          : 4460 (432301 expanded)
%              Number of equality atoms :  136 (3138 expanded)
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X36 ) )
      | ( m1_pre_topc @ X34 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
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

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('51',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
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

thf('62',plain,(
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

thf('63',plain,(
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
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
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
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('74',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('79',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
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
    inference(simplify,[status(thm)],['62'])).

thf('93',plain,
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
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('95',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('101',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('114',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','114'])).

thf('116',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['89','90'])).

thf('117',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('120',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('122',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','122'])).

thf('124',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('127',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('129',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['124','131'])).

thf('133',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('134',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['89','90'])).

thf('136',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('139',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('141',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('143',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('146',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('148',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('149',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('150',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','153'])).

thf('155',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','156'])).

thf('158',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('159',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('160',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('162',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('164',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('165',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('166',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('172',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['170','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['69','169','181'])).

thf('183',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','182'])).

thf('184',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('185',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('186',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['183','186'])).

thf('188',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('190',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('191',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('193',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
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
    inference(simplify,[status(thm)],['62'])).

thf('198',plain,
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
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('200',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('201',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('206',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['203','209'])).

thf('211',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['190','212'])).

thf('214',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('215',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['189','215'])).

thf('217',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['194','195'])).

thf('218',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('219',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('221',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('223',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['216','223'])).

thf('225',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('226',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('227',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('228',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('230',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['225','230'])).

thf('232',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('233',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('235',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('236',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['234','237'])).

thf('239',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['194','195'])).

thf('240',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('241',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('243',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('245',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['238','245'])).

thf('247',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['233','246'])).

thf('248',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('250',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('252',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('253',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('254',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['250','251','252','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['224','257'])).

thf('259',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('260',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('262',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['188','262'])).

thf('264',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('265',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('266',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('268',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('270',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('271',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('272',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['268','269','270','271'])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['187','275'])).

thf('277',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('278',plain,
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
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('281',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['278','279','280','281'])).

thf('283',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['283','284'])).

thf('286',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('289',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('290',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','287','288','289'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('291',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','292'])).

thf('294',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('295',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('296',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('297',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('299',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('304',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['302','308'])).

thf('310',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['309'])).

thf('311',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['310','311'])).

thf('313',plain,(
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
    inference(simplify,[status(thm)],['62'])).

thf('314',plain,
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
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('316',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('317',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('318',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['314','315','316','317'])).

thf('319',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('321',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('322',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('323',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('325',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['323','324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['320','326'])).

thf('328',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['327'])).

thf('329',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['319','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['296','333'])).

thf('335',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('336',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('337',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['295','336'])).

thf('338',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['310','311'])).

thf('339',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('340',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['338','339'])).

thf('341',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('342',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['340','341'])).

thf('343',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('344',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['337','344'])).

thf('346',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('347',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('348',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['331','332'])).

thf('349',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['347','348'])).

thf('350',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('351',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['349','350'])).

thf('352',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['346','351'])).

thf('353',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('354',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['352','353'])).

thf('355',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['352','353'])).

thf('356',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('357',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['355','356'])).

thf('358',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['310','311'])).

thf('359',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('360',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('362',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['360','361'])).

thf('363',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['340','341'])).

thf('364',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['362','363'])).

thf('365',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['357','364'])).

thf('366',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['354','365'])).

thf('367',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['366'])).

thf('368',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('369',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('371',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('372',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('373',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['369','370','371','372'])).

thf('374',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['373'])).

thf('375',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['374','375'])).

thf('377',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['345','376'])).

thf('378',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('379',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['377','378'])).

thf('380',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('381',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['294','381'])).

thf('383',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('384',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('385',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['382','383','384'])).

thf('386',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('387',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['385','386'])).

thf('388',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('389',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('390',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('391',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['387','388','389','390'])).

thf('392',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['391'])).

thf('393',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['392','393'])).

thf('395',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('396',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('397',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['395','396'])).

thf('398',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['397','398'])).

thf('400',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['394','399'])).

thf('401',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('402',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['400','401'])).

thf('403',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['293','402'])).

thf('404',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['404'])).

thf('406',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['403','405'])).

thf('407',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('408',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('409',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('410',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('411',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['409','410'])).

thf('412',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('413',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('414',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['411','412','413'])).

thf('415',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('416',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['414','415'])).

thf('417',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('418',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('419',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['416','417','418'])).

thf('420',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['408','419'])).

thf('421',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('422',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['420','421'])).

thf('423',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['407','422'])).

thf('424',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('425',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['423','424'])).

thf('426',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('427',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['425','426'])).

thf('428',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['400','401'])).

thf('429',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['427','428'])).

thf('430',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('431',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['429','430'])).

thf('432',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('433',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('434',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['431','432','433'])).

thf('435',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['404'])).

thf('436',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['434','435'])).

thf('437',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['293','402'])).

thf('438',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('439',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['437','438'])).

thf('440',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('441',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('442',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['439','440','441'])).

thf('443',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['404'])).

thf('444',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['442','443'])).

thf('445',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['404'])).

thf('446',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['427','428'])).

thf('447',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['404'])).

thf('448',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['446','447'])).

thf('449',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('450',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['406','436','444','445','448','449'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bSVHbz7jGF
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:45:29 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 1.81/2.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.81/2.06  % Solved by: fo/fo7.sh
% 1.81/2.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.06  % done 3873 iterations in 1.608s
% 1.81/2.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.81/2.06  % SZS output start Refutation
% 1.81/2.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.81/2.06  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.81/2.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.81/2.06  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.81/2.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.81/2.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.81/2.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.81/2.06  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.81/2.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.81/2.06  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.81/2.06  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.81/2.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.81/2.06  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.81/2.06  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.81/2.06  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.81/2.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.06  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.81/2.06  thf(sk_B_type, type, sk_B: $i).
% 1.81/2.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.81/2.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.81/2.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.81/2.06  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.81/2.06  thf(d3_struct_0, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.81/2.06  thf('0', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('1', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf(t24_tmap_1, conjecture,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.81/2.06       ( ![B:$i]:
% 1.81/2.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.81/2.06           ( ![C:$i]:
% 1.81/2.06             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.06               ( ![D:$i]:
% 1.81/2.06                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.81/2.06                   ( ( m1_pre_topc @ B @ C ) =>
% 1.81/2.06                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 1.81/2.06                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 1.81/2.06                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.06  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.06    (~( ![A:$i]:
% 1.81/2.06        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.81/2.06            ( l1_pre_topc @ A ) ) =>
% 1.81/2.06          ( ![B:$i]:
% 1.81/2.06            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.81/2.06              ( ![C:$i]:
% 1.81/2.06                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.06                  ( ![D:$i]:
% 1.81/2.06                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.81/2.06                      ( ( m1_pre_topc @ B @ C ) =>
% 1.81/2.06                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 1.81/2.06                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 1.81/2.06                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 1.81/2.06    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 1.81/2.06  thf('2', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('3', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('split', [status(esa)], ['2'])).
% 1.81/2.06  thf(d3_tsep_1, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( l1_struct_0 @ A ) =>
% 1.81/2.06       ( ![B:$i]:
% 1.81/2.06         ( ( l1_struct_0 @ B ) =>
% 1.81/2.06           ( ( r1_tsep_1 @ A @ B ) <=>
% 1.81/2.06             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.81/2.06  thf('4', plain,
% 1.81/2.06      (![X27 : $i, X28 : $i]:
% 1.81/2.06         (~ (l1_struct_0 @ X27)
% 1.81/2.06          | ~ (r1_tsep_1 @ X28 @ X27)
% 1.81/2.06          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.81/2.06          | ~ (l1_struct_0 @ X28))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.81/2.06  thf('5', plain,
% 1.81/2.06      (((~ (l1_struct_0 @ sk_D_2)
% 1.81/2.06         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['3', '4'])).
% 1.81/2.06  thf('6', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf(dt_m1_pre_topc, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( l1_pre_topc @ A ) =>
% 1.81/2.06       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.81/2.06  thf('7', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('8', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['6', '7'])).
% 1.81/2.06  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('10', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf(dt_l1_pre_topc, axiom,
% 1.81/2.06    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.81/2.06  thf('11', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('12', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('14', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['13', '14'])).
% 1.81/2.06  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('18', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('19', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('20', plain,
% 1.81/2.06      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['5', '12', '19'])).
% 1.81/2.06  thf('21', plain,
% 1.81/2.06      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['1', '20'])).
% 1.81/2.06  thf('22', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('23', plain,
% 1.81/2.06      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['21', '22'])).
% 1.81/2.06  thf('24', plain,
% 1.81/2.06      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 1.81/2.06         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['0', '23'])).
% 1.81/2.06  thf('25', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('26', plain,
% 1.81/2.06      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['24', '25'])).
% 1.81/2.06  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('28', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf(d10_xboole_0, axiom,
% 1.81/2.06    (![A:$i,B:$i]:
% 1.81/2.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.81/2.06  thf('29', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.81/2.06      inference('simplify', [status(thm)], ['29'])).
% 1.81/2.06  thf(t4_tsep_1, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.81/2.06       ( ![B:$i]:
% 1.81/2.06         ( ( m1_pre_topc @ B @ A ) =>
% 1.81/2.06           ( ![C:$i]:
% 1.81/2.06             ( ( m1_pre_topc @ C @ A ) =>
% 1.81/2.06               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.81/2.06                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.81/2.06  thf('31', plain,
% 1.81/2.06      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X34 @ X35)
% 1.81/2.06          | ~ (r1_tarski @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X36))
% 1.81/2.06          | (m1_pre_topc @ X34 @ X36)
% 1.81/2.06          | ~ (m1_pre_topc @ X36 @ X35)
% 1.81/2.06          | ~ (l1_pre_topc @ X35)
% 1.81/2.06          | ~ (v2_pre_topc @ X35))),
% 1.81/2.06      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.81/2.06  thf('32', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]:
% 1.81/2.06         (~ (v2_pre_topc @ X1)
% 1.81/2.06          | ~ (l1_pre_topc @ X1)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ X1)
% 1.81/2.06          | (m1_pre_topc @ X0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['30', '31'])).
% 1.81/2.06  thf('33', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]:
% 1.81/2.06         ((m1_pre_topc @ X0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ X1)
% 1.81/2.06          | ~ (l1_pre_topc @ X1)
% 1.81/2.06          | ~ (v2_pre_topc @ X1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['32'])).
% 1.81/2.06  thf('34', plain,
% 1.81/2.06      ((~ (v2_pre_topc @ sk_A)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_A)
% 1.81/2.06        | (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['28', '33'])).
% 1.81/2.06  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('37', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf(dt_k1_tsep_1, axiom,
% 1.81/2.06    (![A:$i,B:$i,C:$i]:
% 1.81/2.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.81/2.06         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.81/2.06         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.06       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.81/2.06         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.81/2.06         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.81/2.06  thf('38', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('39', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1)
% 1.81/2.06          | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['37', '38'])).
% 1.81/2.06  thf('40', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('41', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['39', '40'])).
% 1.81/2.06  thf('42', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['41'])).
% 1.81/2.06  thf('43', plain,
% 1.81/2.06      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['27', '42'])).
% 1.81/2.06  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('45', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1))),
% 1.81/2.06      inference('clc', [status(thm)], ['43', '44'])).
% 1.81/2.06  thf('46', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('47', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 1.81/2.06      inference('clc', [status(thm)], ['45', '46'])).
% 1.81/2.06  thf(d9_pre_topc, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( l1_pre_topc @ A ) =>
% 1.81/2.06       ( ![B:$i]:
% 1.81/2.06         ( ( l1_pre_topc @ B ) =>
% 1.81/2.06           ( ( m1_pre_topc @ B @ A ) <=>
% 1.81/2.06             ( ( ![C:$i]:
% 1.81/2.06                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.81/2.06                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 1.81/2.06                     ( ?[D:$i]:
% 1.81/2.06                       ( ( m1_subset_1 @
% 1.81/2.06                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.81/2.06                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 1.81/2.06                         ( ( C ) =
% 1.81/2.06                           ( k9_subset_1 @
% 1.81/2.06                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 1.81/2.06               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 1.81/2.06  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.81/2.06  thf(zf_stmt_2, axiom,
% 1.81/2.06    (![D:$i,C:$i,B:$i,A:$i]:
% 1.81/2.06     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 1.81/2.06       ( ( ( C ) =
% 1.81/2.06           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 1.81/2.06         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 1.81/2.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.81/2.06  thf(zf_stmt_3, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( l1_pre_topc @ A ) =>
% 1.81/2.06       ( ![B:$i]:
% 1.81/2.06         ( ( l1_pre_topc @ B ) =>
% 1.81/2.06           ( ( m1_pre_topc @ B @ A ) <=>
% 1.81/2.06             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 1.81/2.06               ( ![C:$i]:
% 1.81/2.06                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.81/2.06                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 1.81/2.06                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.06  thf('48', plain,
% 1.81/2.06      (![X15 : $i, X16 : $i]:
% 1.81/2.06         (~ (l1_pre_topc @ X15)
% 1.81/2.06          | ~ (m1_pre_topc @ X15 @ X16)
% 1.81/2.06          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.81/2.06          | ~ (l1_pre_topc @ X16))),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.81/2.06  thf('49', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 1.81/2.06           (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['47', '48'])).
% 1.81/2.06  thf('50', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('51', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 1.81/2.06         (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['49', '50'])).
% 1.81/2.06  thf('52', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 1.81/2.06      inference('clc', [status(thm)], ['45', '46'])).
% 1.81/2.06  thf('53', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('54', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['52', '53'])).
% 1.81/2.06  thf('55', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('56', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['54', '55'])).
% 1.81/2.06  thf('57', plain,
% 1.81/2.06      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 1.81/2.06        (k2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['51', '56'])).
% 1.81/2.06  thf('58', plain,
% 1.81/2.06      (![X0 : $i, X2 : $i]:
% 1.81/2.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('59', plain,
% 1.81/2.06      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 1.81/2.06           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))
% 1.81/2.06        | ((k2_struct_0 @ sk_C_1)
% 1.81/2.06            = (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))))),
% 1.81/2.06      inference('sup-', [status(thm)], ['57', '58'])).
% 1.81/2.06  thf('60', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('61', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 1.81/2.06      inference('clc', [status(thm)], ['45', '46'])).
% 1.81/2.06  thf(d2_tsep_1, axiom,
% 1.81/2.06    (![A:$i]:
% 1.81/2.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.81/2.06       ( ![B:$i]:
% 1.81/2.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.81/2.06           ( ![C:$i]:
% 1.81/2.06             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.06               ( ![D:$i]:
% 1.81/2.06                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.81/2.06                     ( m1_pre_topc @ D @ A ) ) =>
% 1.81/2.06                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.81/2.06                     ( ( u1_struct_0 @ D ) =
% 1.81/2.06                       ( k2_xboole_0 @
% 1.81/2.06                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.06  thf('62', plain,
% 1.81/2.06      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.81/2.06         ((v2_struct_0 @ X23)
% 1.81/2.06          | ~ (m1_pre_topc @ X23 @ X24)
% 1.81/2.06          | (v2_struct_0 @ X25)
% 1.81/2.06          | ~ (v1_pre_topc @ X25)
% 1.81/2.06          | ~ (m1_pre_topc @ X25 @ X24)
% 1.81/2.06          | ((X25) != (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | ((u1_struct_0 @ X25)
% 1.81/2.06              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.81/2.06          | ~ (m1_pre_topc @ X26 @ X24)
% 1.81/2.06          | (v2_struct_0 @ X26)
% 1.81/2.06          | ~ (l1_pre_topc @ X24)
% 1.81/2.06          | (v2_struct_0 @ X24))),
% 1.81/2.06      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.81/2.06  thf('63', plain,
% 1.81/2.06      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.81/2.06         ((v2_struct_0 @ X24)
% 1.81/2.06          | ~ (l1_pre_topc @ X24)
% 1.81/2.06          | (v2_struct_0 @ X26)
% 1.81/2.06          | ~ (m1_pre_topc @ X26 @ X24)
% 1.81/2.06          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.81/2.06          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.81/2.06          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | ~ (m1_pre_topc @ X23 @ X24)
% 1.81/2.06          | (v2_struct_0 @ X23))),
% 1.81/2.06      inference('simplify', [status(thm)], ['62'])).
% 1.81/2.06  thf('64', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['61', '63'])).
% 1.81/2.06  thf('65', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('67', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('68', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 1.81/2.06  thf('69', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['68'])).
% 1.81/2.06  thf('70', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('71', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('72', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('73', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]:
% 1.81/2.06         ((m1_pre_topc @ X0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ X1)
% 1.81/2.06          | ~ (l1_pre_topc @ X1)
% 1.81/2.06          | ~ (v2_pre_topc @ X1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['32'])).
% 1.81/2.06  thf('74', plain,
% 1.81/2.06      ((~ (v2_pre_topc @ sk_A)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_A)
% 1.81/2.06        | (m1_pre_topc @ sk_B @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['72', '73'])).
% 1.81/2.06  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('78', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('79', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('80', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_B)
% 1.81/2.06          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['78', '79'])).
% 1.81/2.06  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('82', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('83', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['81', '82'])).
% 1.81/2.06  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('86', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['80', '85'])).
% 1.81/2.06  thf('87', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B))),
% 1.81/2.06      inference('simplify', [status(thm)], ['86'])).
% 1.81/2.06  thf('88', plain,
% 1.81/2.06      (((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['77', '87'])).
% 1.81/2.06  thf('89', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B))),
% 1.81/2.06      inference('simplify', [status(thm)], ['88'])).
% 1.81/2.06  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('91', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 1.81/2.06      inference('clc', [status(thm)], ['89', '90'])).
% 1.81/2.06  thf('92', plain,
% 1.81/2.06      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.81/2.06         ((v2_struct_0 @ X24)
% 1.81/2.06          | ~ (l1_pre_topc @ X24)
% 1.81/2.06          | (v2_struct_0 @ X26)
% 1.81/2.06          | ~ (m1_pre_topc @ X26 @ X24)
% 1.81/2.06          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.81/2.06          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.81/2.06          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | ~ (m1_pre_topc @ X23 @ X24)
% 1.81/2.06          | (v2_struct_0 @ X23))),
% 1.81/2.06      inference('simplify', [status(thm)], ['62'])).
% 1.81/2.06  thf('93', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['91', '92'])).
% 1.81/2.06  thf('94', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('95', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('97', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 1.81/2.06  thf('98', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('simplify', [status(thm)], ['97'])).
% 1.81/2.06  thf('99', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('100', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('101', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('102', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_B)
% 1.81/2.06          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['100', '101'])).
% 1.81/2.06  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('104', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['102', '103'])).
% 1.81/2.06  thf('105', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_B)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['104'])).
% 1.81/2.06  thf('106', plain,
% 1.81/2.06      (((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['99', '105'])).
% 1.81/2.06  thf('107', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B) | (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['106'])).
% 1.81/2.06  thf('108', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('109', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.81/2.06      inference('clc', [status(thm)], ['107', '108'])).
% 1.81/2.06  thf('110', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['98', '109'])).
% 1.81/2.06  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('112', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.06      inference('clc', [status(thm)], ['110', '111'])).
% 1.81/2.06  thf(t7_xboole_1, axiom,
% 1.81/2.06    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.81/2.06  thf('113', plain,
% 1.81/2.06      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.81/2.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.81/2.06  thf('114', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.06         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['112', '113'])).
% 1.81/2.06  thf('115', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.06         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['71', '114'])).
% 1.81/2.06  thf('116', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 1.81/2.06      inference('clc', [status(thm)], ['89', '90'])).
% 1.81/2.06  thf('117', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('118', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_B)
% 1.81/2.06        | (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['116', '117'])).
% 1.81/2.06  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('120', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['118', '119'])).
% 1.81/2.06  thf('121', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('122', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['120', '121'])).
% 1.81/2.06  thf('123', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.06         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['115', '122'])).
% 1.81/2.06  thf('124', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('125', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('126', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.06         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['112', '113'])).
% 1.81/2.06  thf('127', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.81/2.06         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['125', '126'])).
% 1.81/2.06  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('129', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.06      inference('sup-', [status(thm)], ['128', '129'])).
% 1.81/2.06  thf('131', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.81/2.06         (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['127', '130'])).
% 1.81/2.06  thf('132', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.81/2.06         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['124', '131'])).
% 1.81/2.06  thf('133', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['120', '121'])).
% 1.81/2.06  thf('134', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.81/2.06         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['132', '133'])).
% 1.81/2.06  thf('135', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 1.81/2.06      inference('clc', [status(thm)], ['89', '90'])).
% 1.81/2.06  thf('136', plain,
% 1.81/2.06      (![X15 : $i, X16 : $i]:
% 1.81/2.06         (~ (l1_pre_topc @ X15)
% 1.81/2.06          | ~ (m1_pre_topc @ X15 @ X16)
% 1.81/2.06          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.81/2.06          | ~ (l1_pre_topc @ X16))),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.81/2.06  thf('137', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_B)
% 1.81/2.06        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 1.81/2.06           (k2_struct_0 @ sk_B))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['135', '136'])).
% 1.81/2.06  thf('138', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('139', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 1.81/2.06         (k2_struct_0 @ sk_B))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['137', '138'])).
% 1.81/2.06  thf('140', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['118', '119'])).
% 1.81/2.06  thf('141', plain,
% 1.81/2.06      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 1.81/2.06        (k2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['139', '140'])).
% 1.81/2.06  thf('142', plain,
% 1.81/2.06      (![X0 : $i, X2 : $i]:
% 1.81/2.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('143', plain,
% 1.81/2.06      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 1.81/2.06           (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | ((k2_struct_0 @ sk_B)
% 1.81/2.06            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 1.81/2.06      inference('sup-', [status(thm)], ['141', '142'])).
% 1.81/2.06  thf('144', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ((k2_struct_0 @ sk_B)
% 1.81/2.06            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 1.81/2.06      inference('sup-', [status(thm)], ['134', '143'])).
% 1.81/2.06  thf('145', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('146', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_B)
% 1.81/2.06          = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['144', '145'])).
% 1.81/2.06  thf('147', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('148', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('149', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('150', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_B)
% 1.81/2.06          = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 1.81/2.06  thf('151', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | ((k2_struct_0 @ sk_B)
% 1.81/2.06            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 1.81/2.06      inference('simplify', [status(thm)], ['150'])).
% 1.81/2.06  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('153', plain,
% 1.81/2.06      (((k2_struct_0 @ sk_B) = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('clc', [status(thm)], ['151', '152'])).
% 1.81/2.06  thf('154', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['123', '153'])).
% 1.81/2.06  thf('155', plain,
% 1.81/2.06      (![X0 : $i, X2 : $i]:
% 1.81/2.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('156', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 1.81/2.06        | ~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.81/2.06        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['154', '155'])).
% 1.81/2.06  thf('157', plain,
% 1.81/2.06      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_B)
% 1.81/2.06        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['70', '156'])).
% 1.81/2.06  thf('158', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.81/2.06      inference('simplify', [status(thm)], ['29'])).
% 1.81/2.06  thf('159', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.06      inference('sup-', [status(thm)], ['128', '129'])).
% 1.81/2.06  thf('160', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.81/2.06  thf('161', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('162', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['160', '161'])).
% 1.81/2.06  thf('163', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('164', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.06  thf('165', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.81/2.06      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.06  thf('166', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 1.81/2.06  thf('167', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B) | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['166'])).
% 1.81/2.06  thf('168', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('169', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 1.81/2.06      inference('clc', [status(thm)], ['167', '168'])).
% 1.81/2.06  thf('170', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('171', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('172', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('173', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1)
% 1.81/2.06          | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['171', '172'])).
% 1.81/2.06  thf('174', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('175', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['173', '174'])).
% 1.81/2.06  thf('176', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['175'])).
% 1.81/2.06  thf('177', plain,
% 1.81/2.06      (((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['170', '176'])).
% 1.81/2.06  thf('178', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('179', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 1.81/2.06      inference('clc', [status(thm)], ['177', '178'])).
% 1.81/2.06  thf('180', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('181', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.81/2.06      inference('clc', [status(thm)], ['179', '180'])).
% 1.81/2.06  thf('182', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['69', '169', '181'])).
% 1.81/2.06  thf('183', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup+', [status(thm)], ['60', '182'])).
% 1.81/2.06  thf('184', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['54', '55'])).
% 1.81/2.06  thf('185', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('186', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['184', '185'])).
% 1.81/2.06  thf('187', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['183', '186'])).
% 1.81/2.06  thf('188', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('189', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('190', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('191', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('192', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['41'])).
% 1.81/2.06  thf('193', plain,
% 1.81/2.06      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['191', '192'])).
% 1.81/2.06  thf('194', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['193'])).
% 1.81/2.06  thf('195', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('196', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 1.81/2.06      inference('clc', [status(thm)], ['194', '195'])).
% 1.81/2.06  thf('197', plain,
% 1.81/2.06      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.81/2.06         ((v2_struct_0 @ X24)
% 1.81/2.06          | ~ (l1_pre_topc @ X24)
% 1.81/2.06          | (v2_struct_0 @ X26)
% 1.81/2.06          | ~ (m1_pre_topc @ X26 @ X24)
% 1.81/2.06          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.81/2.06          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.81/2.06          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | ~ (m1_pre_topc @ X23 @ X24)
% 1.81/2.06          | (v2_struct_0 @ X23))),
% 1.81/2.06      inference('simplify', [status(thm)], ['62'])).
% 1.81/2.06  thf('198', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['196', '197'])).
% 1.81/2.06  thf('199', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('200', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('201', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('202', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 1.81/2.06  thf('203', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['202'])).
% 1.81/2.06  thf('204', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('205', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_C_1)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['175'])).
% 1.81/2.06  thf('206', plain,
% 1.81/2.06      (((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['204', '205'])).
% 1.81/2.06  thf('207', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['206'])).
% 1.81/2.06  thf('208', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('209', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('clc', [status(thm)], ['207', '208'])).
% 1.81/2.06  thf('210', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['203', '209'])).
% 1.81/2.06  thf('211', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('212', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))))),
% 1.81/2.06      inference('clc', [status(thm)], ['210', '211'])).
% 1.81/2.06  thf('213', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['190', '212'])).
% 1.81/2.06  thf('214', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('215', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['213', '214'])).
% 1.81/2.06  thf('216', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['189', '215'])).
% 1.81/2.06  thf('217', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 1.81/2.06      inference('clc', [status(thm)], ['194', '195'])).
% 1.81/2.06  thf('218', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('219', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['217', '218'])).
% 1.81/2.06  thf('220', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('221', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['219', '220'])).
% 1.81/2.06  thf('222', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('223', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['221', '222'])).
% 1.81/2.06  thf('224', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['216', '223'])).
% 1.81/2.06  thf('225', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('226', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('227', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))))),
% 1.81/2.06      inference('clc', [status(thm)], ['210', '211'])).
% 1.81/2.06  thf('228', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['226', '227'])).
% 1.81/2.06  thf('229', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('230', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['228', '229'])).
% 1.81/2.06  thf('231', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['225', '230'])).
% 1.81/2.06  thf('232', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['221', '222'])).
% 1.81/2.06  thf('233', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['231', '232'])).
% 1.81/2.06  thf('234', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['231', '232'])).
% 1.81/2.06  thf('235', plain,
% 1.81/2.06      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.81/2.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.81/2.06  thf('236', plain,
% 1.81/2.06      (![X0 : $i, X2 : $i]:
% 1.81/2.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('237', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]:
% 1.81/2.06         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.81/2.06          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['235', '236'])).
% 1.81/2.06  thf('238', plain,
% 1.81/2.06      ((~ (r1_tarski @ 
% 1.81/2.06           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.81/2.06           (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06            = (k2_struct_0 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['234', '237'])).
% 1.81/2.06  thf('239', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 1.81/2.06      inference('clc', [status(thm)], ['194', '195'])).
% 1.81/2.06  thf('240', plain,
% 1.81/2.06      (![X15 : $i, X16 : $i]:
% 1.81/2.06         (~ (l1_pre_topc @ X15)
% 1.81/2.06          | ~ (m1_pre_topc @ X15 @ X16)
% 1.81/2.06          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.81/2.06          | ~ (l1_pre_topc @ X16))),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.81/2.06  thf('241', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (r1_tarski @ 
% 1.81/2.06           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.81/2.06           (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['239', '240'])).
% 1.81/2.06  thf('242', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('243', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.81/2.06         (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['241', '242'])).
% 1.81/2.06  thf('244', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['219', '220'])).
% 1.81/2.06  thf('245', plain,
% 1.81/2.06      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 1.81/2.06        (k2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['243', '244'])).
% 1.81/2.06  thf('246', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06            = (k2_struct_0 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['238', '245'])).
% 1.81/2.06  thf('247', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['233', '246'])).
% 1.81/2.06  thf('248', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06            = (k2_struct_0 @ sk_C_1)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['247'])).
% 1.81/2.06  thf('249', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('250', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['248', '249'])).
% 1.81/2.06  thf('251', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('252', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('253', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('254', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06          = (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['250', '251', '252', '253'])).
% 1.81/2.06  thf('255', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06            = (k2_struct_0 @ sk_C_1)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['254'])).
% 1.81/2.06  thf('256', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('257', plain,
% 1.81/2.06      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06         = (k2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('clc', [status(thm)], ['255', '256'])).
% 1.81/2.06  thf('258', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_C_1)
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['224', '257'])).
% 1.81/2.06  thf('259', plain,
% 1.81/2.06      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.81/2.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.81/2.06  thf('260', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['258', '259'])).
% 1.81/2.06  thf('261', plain,
% 1.81/2.06      (![X0 : $i, X2 : $i]:
% 1.81/2.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('262', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 1.81/2.06        | ~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['260', '261'])).
% 1.81/2.06  thf('263', plain,
% 1.81/2.06      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_C_1)
% 1.81/2.06        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['188', '262'])).
% 1.81/2.06  thf('264', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.81/2.06      inference('simplify', [status(thm)], ['29'])).
% 1.81/2.06  thf('265', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('266', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['263', '264', '265'])).
% 1.81/2.06  thf('267', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('268', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['266', '267'])).
% 1.81/2.06  thf('269', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('270', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('271', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('272', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['268', '269', '270', '271'])).
% 1.81/2.06  thf('273', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['272'])).
% 1.81/2.06  thf('274', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('275', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('clc', [status(thm)], ['273', '274'])).
% 1.81/2.06  thf('276', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['187', '275'])).
% 1.81/2.06  thf('277', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('278', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 1.81/2.06      inference('sup-', [status(thm)], ['276', '277'])).
% 1.81/2.06  thf('279', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('280', plain, ((l1_pre_topc @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.06  thf('281', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.81/2.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.81/2.06  thf('282', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_B)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_C_1))),
% 1.81/2.06      inference('demod', [status(thm)], ['278', '279', '280', '281'])).
% 1.81/2.06  thf('283', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06        | (v2_struct_0 @ sk_C_1)
% 1.81/2.06        | (v2_struct_0 @ sk_B))),
% 1.81/2.06      inference('simplify', [status(thm)], ['282'])).
% 1.81/2.06  thf('284', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('285', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_B)
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))))),
% 1.81/2.06      inference('clc', [status(thm)], ['283', '284'])).
% 1.81/2.06  thf('286', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('287', plain,
% 1.81/2.06      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 1.81/2.06      inference('clc', [status(thm)], ['285', '286'])).
% 1.81/2.06  thf('288', plain,
% 1.81/2.06      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.81/2.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.81/2.06  thf('289', plain,
% 1.81/2.06      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 1.81/2.06         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 1.81/2.06      inference('clc', [status(thm)], ['285', '286'])).
% 1.81/2.06  thf('290', plain,
% 1.81/2.06      (((k2_struct_0 @ sk_C_1)
% 1.81/2.06         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 1.81/2.06      inference('demod', [status(thm)], ['59', '287', '288', '289'])).
% 1.81/2.06  thf(t70_xboole_1, axiom,
% 1.81/2.06    (![A:$i,B:$i,C:$i]:
% 1.81/2.06     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.81/2.06            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.81/2.06       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.81/2.06            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.81/2.06  thf('291', plain,
% 1.81/2.06      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.81/2.06         ((r1_xboole_0 @ X3 @ X6)
% 1.81/2.06          | ~ (r1_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X6)))),
% 1.81/2.06      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.81/2.06  thf('292', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 1.81/2.06          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['290', '291'])).
% 1.81/2.06  thf('293', plain,
% 1.81/2.06      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['26', '292'])).
% 1.81/2.06  thf('294', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('295', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('296', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('297', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('298', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]:
% 1.81/2.06         ((m1_pre_topc @ X0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ X1)
% 1.81/2.06          | ~ (l1_pre_topc @ X1)
% 1.81/2.06          | ~ (v2_pre_topc @ X1))),
% 1.81/2.06      inference('simplify', [status(thm)], ['32'])).
% 1.81/2.06  thf('299', plain,
% 1.81/2.06      ((~ (v2_pre_topc @ sk_A)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_A)
% 1.81/2.06        | (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['297', '298'])).
% 1.81/2.06  thf('300', plain, ((v2_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('301', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('302', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('303', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('304', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('305', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2)
% 1.81/2.06          | ~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['303', '304'])).
% 1.81/2.06  thf('306', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('307', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['305', '306'])).
% 1.81/2.06  thf('308', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.81/2.06          | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2))),
% 1.81/2.06      inference('simplify', [status(thm)], ['307'])).
% 1.81/2.06  thf('309', plain,
% 1.81/2.06      (((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['302', '308'])).
% 1.81/2.06  thf('310', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2))),
% 1.81/2.06      inference('simplify', [status(thm)], ['309'])).
% 1.81/2.06  thf('311', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('312', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.81/2.06      inference('clc', [status(thm)], ['310', '311'])).
% 1.81/2.06  thf('313', plain,
% 1.81/2.06      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.81/2.06         ((v2_struct_0 @ X24)
% 1.81/2.06          | ~ (l1_pre_topc @ X24)
% 1.81/2.06          | (v2_struct_0 @ X26)
% 1.81/2.06          | ~ (m1_pre_topc @ X26 @ X24)
% 1.81/2.06          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 1.81/2.06          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 1.81/2.06          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 1.81/2.06          | ~ (m1_pre_topc @ X23 @ X24)
% 1.81/2.06          | (v2_struct_0 @ X23))),
% 1.81/2.06      inference('simplify', [status(thm)], ['62'])).
% 1.81/2.06  thf('314', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['312', '313'])).
% 1.81/2.06  thf('315', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('316', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('317', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('318', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['314', '315', '316', '317'])).
% 1.81/2.06  thf('319', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('simplify', [status(thm)], ['318'])).
% 1.81/2.06  thf('320', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('321', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('322', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('323', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2)
% 1.81/2.06          | ~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['321', '322'])).
% 1.81/2.06  thf('324', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('325', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['323', '324'])).
% 1.81/2.06  thf('326', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         ((v2_struct_0 @ sk_D_2)
% 1.81/2.06          | (v2_struct_0 @ X0)
% 1.81/2.06          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 1.81/2.06          | (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['325'])).
% 1.81/2.06  thf('327', plain,
% 1.81/2.06      (((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['320', '326'])).
% 1.81/2.06  thf('328', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['327'])).
% 1.81/2.06  thf('329', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('330', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('clc', [status(thm)], ['328', '329'])).
% 1.81/2.06  thf('331', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['319', '330'])).
% 1.81/2.06  thf('332', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('333', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))))),
% 1.81/2.06      inference('clc', [status(thm)], ['331', '332'])).
% 1.81/2.06  thf('334', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['296', '333'])).
% 1.81/2.06  thf('335', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('336', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['334', '335'])).
% 1.81/2.06  thf('337', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['295', '336'])).
% 1.81/2.06  thf('338', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.81/2.06      inference('clc', [status(thm)], ['310', '311'])).
% 1.81/2.06  thf('339', plain,
% 1.81/2.06      (![X21 : $i, X22 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X21 @ X22)
% 1.81/2.06          | (l1_pre_topc @ X21)
% 1.81/2.06          | ~ (l1_pre_topc @ X22))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.06  thf('340', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06        | (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['338', '339'])).
% 1.81/2.06  thf('341', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('342', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['340', '341'])).
% 1.81/2.06  thf('343', plain,
% 1.81/2.06      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.06  thf('344', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['342', '343'])).
% 1.81/2.06  thf('345', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['337', '344'])).
% 1.81/2.06  thf('346', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('347', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('348', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06            = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))))),
% 1.81/2.06      inference('clc', [status(thm)], ['331', '332'])).
% 1.81/2.06  thf('349', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['347', '348'])).
% 1.81/2.06  thf('350', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('351', plain,
% 1.81/2.06      ((((u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['349', '350'])).
% 1.81/2.06  thf('352', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['346', '351'])).
% 1.81/2.06  thf('353', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['342', '343'])).
% 1.81/2.06  thf('354', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['352', '353'])).
% 1.81/2.06  thf('355', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['352', '353'])).
% 1.81/2.06  thf('356', plain,
% 1.81/2.06      (![X0 : $i, X1 : $i]:
% 1.81/2.06         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.81/2.06          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['235', '236'])).
% 1.81/2.06  thf('357', plain,
% 1.81/2.06      ((~ (r1_tarski @ 
% 1.81/2.06           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.81/2.06           (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.81/2.06            = (k2_struct_0 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['355', '356'])).
% 1.81/2.06  thf('358', plain,
% 1.81/2.06      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 1.81/2.06      inference('clc', [status(thm)], ['310', '311'])).
% 1.81/2.06  thf('359', plain,
% 1.81/2.06      (![X15 : $i, X16 : $i]:
% 1.81/2.06         (~ (l1_pre_topc @ X15)
% 1.81/2.06          | ~ (m1_pre_topc @ X15 @ X16)
% 1.81/2.06          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 1.81/2.06          | ~ (l1_pre_topc @ X16))),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.81/2.06  thf('360', plain,
% 1.81/2.06      ((~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06        | (r1_tarski @ 
% 1.81/2.06           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.81/2.06           (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['358', '359'])).
% 1.81/2.06  thf('361', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('362', plain,
% 1.81/2.06      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.81/2.06         (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['360', '361'])).
% 1.81/2.06  thf('363', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['340', '341'])).
% 1.81/2.06  thf('364', plain,
% 1.81/2.06      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 1.81/2.06        (k2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['362', '363'])).
% 1.81/2.06  thf('365', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((k2_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.81/2.06            = (k2_struct_0 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['357', '364'])).
% 1.81/2.06  thf('366', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['354', '365'])).
% 1.81/2.06  thf('367', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06            = (k2_struct_0 @ sk_D_2)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['366'])).
% 1.81/2.06  thf('368', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('369', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['367', '368'])).
% 1.81/2.06  thf('370', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('371', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('372', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('373', plain,
% 1.81/2.06      ((((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06          = (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['369', '370', '371', '372'])).
% 1.81/2.06  thf('374', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06            = (k2_struct_0 @ sk_D_2)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['373'])).
% 1.81/2.06  thf('375', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('376', plain,
% 1.81/2.06      (((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06         = (k2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('clc', [status(thm)], ['374', '375'])).
% 1.81/2.06  thf('377', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_D_2)
% 1.81/2.06          = (k2_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2)))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['345', '376'])).
% 1.81/2.06  thf('378', plain,
% 1.81/2.06      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.81/2.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.81/2.06  thf('379', plain,
% 1.81/2.06      (((r1_tarski @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['377', '378'])).
% 1.81/2.06  thf('380', plain,
% 1.81/2.06      (![X0 : $i, X2 : $i]:
% 1.81/2.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.81/2.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.06  thf('381', plain,
% 1.81/2.06      (((v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 1.81/2.06        | ~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 1.81/2.06        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['379', '380'])).
% 1.81/2.06  thf('382', plain,
% 1.81/2.06      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 1.81/2.06        | ~ (l1_struct_0 @ sk_D_2)
% 1.81/2.06        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['294', '381'])).
% 1.81/2.06  thf('383', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.81/2.06      inference('simplify', [status(thm)], ['29'])).
% 1.81/2.06  thf('384', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('385', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['382', '383', '384'])).
% 1.81/2.06  thf('386', plain,
% 1.81/2.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.06         (~ (m1_pre_topc @ X29 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X29)
% 1.81/2.06          | ~ (l1_pre_topc @ X30)
% 1.81/2.06          | (v2_struct_0 @ X30)
% 1.81/2.06          | (v2_struct_0 @ X31)
% 1.81/2.06          | ~ (m1_pre_topc @ X31 @ X30)
% 1.81/2.06          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 1.81/2.06      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.81/2.06  thf('387', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.81/2.06        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ~ (l1_pre_topc @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ~ (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['385', '386'])).
% 1.81/2.06  thf('388', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('389', plain, ((l1_pre_topc @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['8', '9'])).
% 1.81/2.06  thf('390', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 1.81/2.06      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.81/2.06  thf('391', plain,
% 1.81/2.06      ((((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2)
% 1.81/2.06        | (v2_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('demod', [status(thm)], ['387', '388', '389', '390'])).
% 1.81/2.06  thf('392', plain,
% 1.81/2.06      (((v2_struct_0 @ sk_D_2)
% 1.81/2.06        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 1.81/2.06      inference('simplify', [status(thm)], ['391'])).
% 1.81/2.06  thf('393', plain, (~ (v2_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('394', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('clc', [status(thm)], ['392', '393'])).
% 1.81/2.06  thf('395', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 1.81/2.06      inference('clc', [status(thm)], ['167', '168'])).
% 1.81/2.06  thf('396', plain,
% 1.81/2.06      (![X27 : $i, X28 : $i]:
% 1.81/2.06         (~ (l1_struct_0 @ X27)
% 1.81/2.06          | ~ (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.81/2.06          | (r1_tsep_1 @ X28 @ X27)
% 1.81/2.06          | ~ (l1_struct_0 @ X28))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.81/2.06  thf('397', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 1.81/2.06          | ~ (l1_struct_0 @ X0)
% 1.81/2.06          | (r1_tsep_1 @ X0 @ sk_B)
% 1.81/2.06          | ~ (l1_struct_0 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['395', '396'])).
% 1.81/2.06  thf('398', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.06      inference('sup-', [status(thm)], ['128', '129'])).
% 1.81/2.06  thf('399', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 1.81/2.06          | ~ (l1_struct_0 @ X0)
% 1.81/2.06          | (r1_tsep_1 @ X0 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['397', '398'])).
% 1.81/2.06  thf('400', plain,
% 1.81/2.06      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 1.81/2.06        | (r1_tsep_1 @ sk_D_2 @ sk_B)
% 1.81/2.06        | ~ (l1_struct_0 @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['394', '399'])).
% 1.81/2.06  thf('401', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('402', plain,
% 1.81/2.06      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 1.81/2.06        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['400', '401'])).
% 1.81/2.06  thf('403', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['293', '402'])).
% 1.81/2.06  thf('404', plain,
% 1.81/2.06      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.81/2.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.06  thf('405', plain,
% 1.81/2.06      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 1.81/2.06      inference('split', [status(esa)], ['404'])).
% 1.81/2.06  thf('406', plain,
% 1.81/2.06      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['403', '405'])).
% 1.81/2.06  thf('407', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('408', plain,
% 1.81/2.06      (![X9 : $i]:
% 1.81/2.06         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.81/2.06  thf('409', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('split', [status(esa)], ['2'])).
% 1.81/2.06  thf(symmetry_r1_tsep_1, axiom,
% 1.81/2.06    (![A:$i,B:$i]:
% 1.81/2.06     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 1.81/2.06       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 1.81/2.06  thf('410', plain,
% 1.81/2.06      (![X32 : $i, X33 : $i]:
% 1.81/2.06         (~ (l1_struct_0 @ X32)
% 1.81/2.06          | ~ (l1_struct_0 @ X33)
% 1.81/2.06          | (r1_tsep_1 @ X33 @ X32)
% 1.81/2.06          | ~ (r1_tsep_1 @ X32 @ X33))),
% 1.81/2.06      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.81/2.06  thf('411', plain,
% 1.81/2.06      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 1.81/2.06         | ~ (l1_struct_0 @ sk_D_2)
% 1.81/2.06         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['409', '410'])).
% 1.81/2.06  thf('412', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('413', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('414', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['411', '412', '413'])).
% 1.81/2.06  thf('415', plain,
% 1.81/2.06      (![X27 : $i, X28 : $i]:
% 1.81/2.06         (~ (l1_struct_0 @ X27)
% 1.81/2.06          | ~ (r1_tsep_1 @ X28 @ X27)
% 1.81/2.06          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.81/2.06          | ~ (l1_struct_0 @ X28))),
% 1.81/2.06      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.81/2.06  thf('416', plain,
% 1.81/2.06      (((~ (l1_struct_0 @ sk_D_2)
% 1.81/2.06         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['414', '415'])).
% 1.81/2.06  thf('417', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('418', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('419', plain,
% 1.81/2.06      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['416', '417', '418'])).
% 1.81/2.06  thf('420', plain,
% 1.81/2.06      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 1.81/2.06         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['408', '419'])).
% 1.81/2.06  thf('421', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('422', plain,
% 1.81/2.06      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['420', '421'])).
% 1.81/2.06  thf('423', plain,
% 1.81/2.06      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 1.81/2.06         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup+', [status(thm)], ['407', '422'])).
% 1.81/2.06  thf('424', plain, ((l1_struct_0 @ sk_C_1)),
% 1.81/2.06      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.06  thf('425', plain,
% 1.81/2.06      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['423', '424'])).
% 1.81/2.06  thf('426', plain,
% 1.81/2.06      (![X0 : $i]:
% 1.81/2.06         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 1.81/2.06          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['290', '291'])).
% 1.81/2.06  thf('427', plain,
% 1.81/2.06      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 1.81/2.06         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['425', '426'])).
% 1.81/2.06  thf('428', plain,
% 1.81/2.06      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 1.81/2.06        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.81/2.06      inference('demod', [status(thm)], ['400', '401'])).
% 1.81/2.06  thf('429', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['427', '428'])).
% 1.81/2.06  thf('430', plain,
% 1.81/2.06      (![X32 : $i, X33 : $i]:
% 1.81/2.06         (~ (l1_struct_0 @ X32)
% 1.81/2.06          | ~ (l1_struct_0 @ X33)
% 1.81/2.06          | (r1_tsep_1 @ X33 @ X32)
% 1.81/2.06          | ~ (r1_tsep_1 @ X32 @ X33))),
% 1.81/2.06      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.81/2.06  thf('431', plain,
% 1.81/2.06      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 1.81/2.06         | ~ (l1_struct_0 @ sk_B)
% 1.81/2.06         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['429', '430'])).
% 1.81/2.06  thf('432', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.06      inference('sup-', [status(thm)], ['128', '129'])).
% 1.81/2.06  thf('433', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('434', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('demod', [status(thm)], ['431', '432', '433'])).
% 1.81/2.06  thf('435', plain,
% 1.81/2.06      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 1.81/2.06      inference('split', [status(esa)], ['404'])).
% 1.81/2.06  thf('436', plain,
% 1.81/2.06      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['434', '435'])).
% 1.81/2.06  thf('437', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['293', '402'])).
% 1.81/2.06  thf('438', plain,
% 1.81/2.06      (![X32 : $i, X33 : $i]:
% 1.81/2.06         (~ (l1_struct_0 @ X32)
% 1.81/2.06          | ~ (l1_struct_0 @ X33)
% 1.81/2.06          | (r1_tsep_1 @ X33 @ X32)
% 1.81/2.06          | ~ (r1_tsep_1 @ X32 @ X33))),
% 1.81/2.06      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.81/2.06  thf('439', plain,
% 1.81/2.06      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 1.81/2.06         | ~ (l1_struct_0 @ sk_B)
% 1.81/2.06         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['437', '438'])).
% 1.81/2.06  thf('440', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.06      inference('sup-', [status(thm)], ['128', '129'])).
% 1.81/2.06  thf('441', plain, ((l1_struct_0 @ sk_D_2)),
% 1.81/2.06      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.06  thf('442', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 1.81/2.06      inference('demod', [status(thm)], ['439', '440', '441'])).
% 1.81/2.06  thf('443', plain,
% 1.81/2.06      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 1.81/2.06      inference('split', [status(esa)], ['404'])).
% 1.81/2.06  thf('444', plain,
% 1.81/2.06      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 1.81/2.06      inference('sup-', [status(thm)], ['442', '443'])).
% 1.81/2.06  thf('445', plain,
% 1.81/2.06      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 1.81/2.06      inference('split', [status(esa)], ['404'])).
% 1.81/2.06  thf('446', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 1.81/2.06      inference('sup-', [status(thm)], ['427', '428'])).
% 1.81/2.06  thf('447', plain,
% 1.81/2.06      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 1.81/2.06      inference('split', [status(esa)], ['404'])).
% 1.81/2.06  thf('448', plain,
% 1.81/2.06      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 1.81/2.06      inference('sup-', [status(thm)], ['446', '447'])).
% 1.81/2.06  thf('449', plain,
% 1.81/2.06      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 1.81/2.06      inference('split', [status(esa)], ['2'])).
% 1.81/2.06  thf('450', plain, ($false),
% 1.81/2.06      inference('sat_resolution*', [status(thm)],
% 1.81/2.06                ['406', '436', '444', '445', '448', '449'])).
% 1.81/2.06  
% 1.81/2.06  % SZS output end Refutation
% 1.81/2.06  
% 1.81/2.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
