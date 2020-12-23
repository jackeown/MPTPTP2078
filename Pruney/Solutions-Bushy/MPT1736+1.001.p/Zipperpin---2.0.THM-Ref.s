%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1736+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l8g3gqDeta

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:10 EST 2020

% Result     : Theorem 48.52s
% Output     : Refutation 48.52s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 852 expanded)
%              Number of leaves         :   42 ( 247 expanded)
%              Depth                    :   44
%              Number of atoms          : 3258 (24357 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t45_tmap_1,conjecture,(
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
                    & ( v1_borsuk_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( ( m1_pre_topc @ B @ D )
                      & ( r1_tsep_1 @ D @ C ) )
                   => ( ( v1_borsuk_1 @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                      & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                      & ( v1_borsuk_1 @ B @ ( k1_tsep_1 @ A @ C @ B ) )
                      & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ C @ B ) ) ) ) ) ) ) ) )).

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
                      & ( v1_borsuk_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( ( m1_pre_topc @ B @ D )
                        & ( r1_tsep_1 @ D @ C ) )
                     => ( ( v1_borsuk_1 @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                        & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                        & ( v1_borsuk_1 @ B @ ( k1_tsep_1 @ A @ C @ B ) )
                        & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_pre_topc @ X18 @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( m1_pre_topc @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_pre_topc @ C @ A )
                & ~ ( v2_struct_0 @ C ) )
             => ! [D: $i] :
                  ( ( ( m1_pre_topc @ D @ A )
                    & ~ ( v2_struct_0 @ D ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ D @ C )
                        & ~ ( r1_tsep_1 @ C @ D ) )
                      | ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_1 @ D @ B )
     => ( ( r1_tsep_1 @ B @ D )
        & ( r1_tsep_1 @ D @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_0 @ D @ C )
     => ( ~ ( r1_tsep_1 @ C @ D )
        & ~ ( r1_tsep_1 @ D @ C ) ) ) )).

thf(zf_stmt_5,axiom,(
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
                   => ( ( zip_tseitin_1 @ D @ B )
                      | ( zip_tseitin_0 @ D @ C ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ sk_B )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ sk_B )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_D )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_D )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( zip_tseitin_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tsep_1 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_tmap_1,axiom,(
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
             => ( ( m1_pre_topc @ B @ C )
               => ( ~ ( r1_tsep_1 @ B @ C )
                  & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X17 )
      | ~ ( r1_tsep_1 @ X15 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ( k1_tsep_1 @ A @ B @ C )
        = ( k1_tsep_1 @ A @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( ( k1_tsep_1 @ X3 @ X2 @ X4 )
        = ( k1_tsep_1 @ X3 @ X4 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k1_tsep_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( k1_tsep_1 @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( k1_tsep_1 @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( m1_pre_topc @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_pre_topc @ C @ A )
                & ~ ( v2_struct_0 @ C ) )
             => ! [D: $i] :
                  ( ( ( m1_pre_topc @ D @ A )
                    & ~ ( v2_struct_0 @ D ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                      | ( ~ ( r1_tsep_1 @ D @ C )
                        & ~ ( r1_tsep_1 @ C @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_3 @ D @ C )
     => ( ~ ( r1_tsep_1 @ C @ D )
        & ~ ( r1_tsep_1 @ D @ C ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ B @ A )
     => ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
        & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) )
          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf(zf_stmt_10,axiom,(
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
                   => ( ( zip_tseitin_3 @ D @ C )
                      | ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( zip_tseitin_2 @ X37 @ X38 @ X35 @ X36 )
      | ( zip_tseitin_3 @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X35 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X36 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_D @ sk_B @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_D @ sk_B @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( zip_tseitin_2 @ sk_C @ sk_D @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_tsep_1 @ X30 @ X31 @ ( k1_tsep_1 @ X30 @ X29 @ X32 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( zip_tseitin_2 @ X32 @ X31 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t43_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_borsuk_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ C @ B )
               => ( ( v1_borsuk_1 @ ( k2_tsep_1 @ A @ C @ B ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ C @ B ) @ B ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ( r1_tsep_1 @ X41 @ X39 )
      | ( v1_borsuk_1 @ ( k2_tsep_1 @ X40 @ X41 @ X39 ) @ X39 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( v1_borsuk_1 @ X41 @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t43_tmap_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_borsuk_1 @ ( k2_tsep_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_borsuk_1 @ ( k2_tsep_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v1_borsuk_1 @ ( k2_tsep_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_borsuk_1 @ sk_D @ sk_A )
    | ( v1_borsuk_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    v1_borsuk_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v1_borsuk_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_borsuk_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','85'])).

thf('87',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_borsuk_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('100',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf(t13_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_borsuk_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('104',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( X13
       != ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( v1_borsuk_1 @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v1_borsuk_1 @ X12 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_tmap_1])).

thf('105',plain,(
    ! [X12: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( v1_borsuk_1 @ X12 @ X14 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) @ X14 )
      | ~ ( v1_borsuk_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_borsuk_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('109',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['96','97'])).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_borsuk_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( v1_borsuk_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['106','112','117','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_borsuk_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','124'])).

thf('126',plain,
    ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','126'])).

thf('128',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','128'])).

thf('130',plain,
    ( ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['49','130'])).

thf('132',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('137',plain,
    ( ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['133'])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('148',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['133'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('157',plain,
    ( ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('158',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['133'])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_3 @ sk_C @ sk_D )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tsep_1 @ X21 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('161',plain,
    ( ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_3 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_3 @ sk_C @ sk_D )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','161'])).

thf('163',plain,
    ( ( ( zip_tseitin_3 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_3 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_3 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( ( zip_tseitin_3 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tsep_1 @ X33 @ X34 )
      | ~ ( zip_tseitin_3 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('173',plain,(
    ~ ( zip_tseitin_3 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['133'])).

thf('184',plain,(
    ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['146','155','182','183'])).

thf('185',plain,(
    ~ ( v1_borsuk_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['134','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','185'])).

thf('187',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tsep_1 @ X21 @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('188',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( zip_tseitin_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','188'])).

thf('190',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ~ ( zip_tseitin_3 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    $false ),
    inference(demod,[status(thm)],['0','205'])).


%------------------------------------------------------------------------------
