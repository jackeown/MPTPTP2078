%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ikY0FSDdmh

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:35 EST 2020

% Result     : Theorem 29.67s
% Output     : Refutation 29.67s
% Verified   : 
% Statistics : Number of formulae       :  297 (1545 expanded)
%              Number of leaves         :   35 ( 436 expanded)
%              Depth                    :   51
%              Number of atoms          : 3895 (44837 expanded)
%              Number of equality atoms :   42 ( 168 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t46_tmap_1,conjecture,(
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
                    & ( v1_tsep_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( ( m1_pre_topc @ B @ D )
                      & ( r1_tsep_1 @ D @ C ) )
                   => ( ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                      & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                      & ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ C @ B ) )
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
                      & ( v1_tsep_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( ( m1_pre_topc @ B @ D )
                        & ( r1_tsep_1 @ D @ C ) )
                     => ( ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                        & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) )
                        & ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ C @ B ) )
                        & ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( ( k1_tsep_1 @ X5 @ X4 @ X6 )
        = ( k1_tsep_1 @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( k1_tsep_1 @ sk_A @ X0 @ sk_B ) )
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
      ( ( ( k1_tsep_1 @ sk_A @ sk_B @ X0 )
        = ( k1_tsep_1 @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_1 @ D @ C )
     => ( ~ ( r1_tsep_1 @ C @ D )
        & ~ ( r1_tsep_1 @ D @ C ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
        & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) )
          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

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
                   => ( ( zip_tseitin_1 @ D @ C )
                      | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( zip_tseitin_0 @ X36 @ X37 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X37 )
      | ~ ( m1_pre_topc @ X34 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( zip_tseitin_0 @ sk_C @ sk_D @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_tsep_1 @ X29 @ X30 @ ( k1_tsep_1 @ X29 @ X28 @ X31 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ~ ( zip_tseitin_0 @ X31 @ X30 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k1_tsep_1 @ X23 @ X22 @ X22 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( ( k1_tsep_1 @ sk_D @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_D @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','47','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_D @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t44_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ C @ B )
               => ( ( v1_tsep_1 @ ( k2_tsep_1 @ A @ C @ B ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ C @ B ) @ B ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X43 )
      | ( r1_tsep_1 @ X44 @ X42 )
      | ( v1_tsep_1 @ ( k2_tsep_1 @ X43 @ X44 @ X42 ) @ X42 )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( v1_tsep_1 @ X44 @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t44_tmap_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_A )
    | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    v1_tsep_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_tsep_1 @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tsep_1 @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_pre_topc @ X19 @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k1_tsep_1 @ X23 @ X22 @ X22 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('86',plain,
    ( ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,
    ( ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','88'])).

thf('90',plain,
    ( ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B )
      = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( m1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( m1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( m1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( m1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k1_tsep_1 @ X23 @ X22 @ X22 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf(t14_tmap_1,axiom,(
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
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_tsep_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( X14
       != ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( v1_tsep_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v1_tsep_1 @ X13 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t14_tmap_1])).

thf('114',plain,(
    ! [X13: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( v1_tsep_1 @ X13 @ X15 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) @ X15 )
      | ~ ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) @ X15 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( v1_tsep_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('125',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('131',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('141',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('142',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('143',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['121','122'])).

thf('144',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) @ X0 )
      | ( v1_tsep_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['115','128','134','139','140','141','142','147'])).

thf('149',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('150',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('151',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tsep_1 @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ X0 )
      | ( v1_tsep_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['148','151','152'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_tsep_1 @ ( k1_tsep_1 @ sk_D @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','154'])).

thf('156',plain,
    ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','156'])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','158'])).

thf('160',plain,
    ( ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','160'])).

thf('162',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['163'])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('167',plain,
    ( ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['163'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('178',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['163'])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['159'])).

thf('187',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['163'])).

thf('188',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf(t39_tmap_1,axiom,(
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
                 => ( ~ ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                        & ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ C @ D ) )
                    & ~ ( ~ ( ( r1_tsep_1 @ B @ D )
                            & ( r1_tsep_1 @ C @ D ) )
                        & ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                    & ~ ( ~ ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                        & ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ D @ C ) )
                    & ~ ( ~ ( ( r1_tsep_1 @ D @ B )
                            & ( r1_tsep_1 @ D @ C ) )
                        & ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) )).

thf('189',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( r1_tsep_1 @ X40 @ ( k1_tsep_1 @ X39 @ X38 @ X41 ) )
      | ( r1_tsep_1 @ X40 @ X38 )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('190',plain,
    ( ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','194','195'])).

thf('197',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('199',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200','201','202'])).

thf('204',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_D ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
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

thf('207',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X16 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','211'])).

thf('213',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','214'])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_D ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tsep_1 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('219',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['163'])).

thf('230',plain,(
    ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['176','185','228','229'])).

thf('231',plain,(
    ~ ( v1_tsep_1 @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['164','230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','231'])).

thf('233',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( r1_tsep_1 @ X40 @ ( k1_tsep_1 @ X39 @ X38 @ X41 ) )
      | ( r1_tsep_1 @ X40 @ X38 )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('234',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['234','235','236','237','238','239'])).

thf('241',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('243',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['243','244','245','246'])).

thf('248',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('250',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,(
    $false ),
    inference(demod,[status(thm)],['0','259'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ikY0FSDdmh
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 29.67/29.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.67/29.86  % Solved by: fo/fo7.sh
% 29.67/29.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.67/29.86  % done 12131 iterations in 29.393s
% 29.67/29.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.67/29.86  % SZS output start Refutation
% 29.67/29.86  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 29.67/29.86  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 29.67/29.86  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 29.67/29.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 29.67/29.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 29.67/29.86  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 29.67/29.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 29.67/29.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 29.67/29.86  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 29.67/29.86  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 29.67/29.86  thf(sk_A_type, type, sk_A: $i).
% 29.67/29.86  thf(sk_D_type, type, sk_D: $i).
% 29.67/29.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 29.67/29.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 29.67/29.86  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 29.67/29.86  thf(sk_C_type, type, sk_C: $i).
% 29.67/29.86  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 29.67/29.86  thf(sk_B_type, type, sk_B: $i).
% 29.67/29.86  thf(t46_tmap_1, conjecture,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.86       ( ![B:$i]:
% 29.67/29.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.86           ( ![C:$i]:
% 29.67/29.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86               ( ![D:$i]:
% 29.67/29.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 29.67/29.86                     ( m1_pre_topc @ D @ A ) ) =>
% 29.67/29.86                   ( ( ( m1_pre_topc @ B @ D ) & ( r1_tsep_1 @ D @ C ) ) =>
% 29.67/29.86                     ( ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 29.67/29.86                       ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 29.67/29.86                       ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ C @ B ) ) & 
% 29.67/29.86                       ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ C @ B ) ) ) ) ) ) ) ) ) ) ))).
% 29.67/29.86  thf(zf_stmt_0, negated_conjecture,
% 29.67/29.86    (~( ![A:$i]:
% 29.67/29.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 29.67/29.86            ( l1_pre_topc @ A ) ) =>
% 29.67/29.86          ( ![B:$i]:
% 29.67/29.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.86              ( ![C:$i]:
% 29.67/29.86                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86                  ( ![D:$i]:
% 29.67/29.86                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 29.67/29.86                        ( m1_pre_topc @ D @ A ) ) =>
% 29.67/29.86                      ( ( ( m1_pre_topc @ B @ D ) & ( r1_tsep_1 @ D @ C ) ) =>
% 29.67/29.86                        ( ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 29.67/29.86                          ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 29.67/29.86                          ( v1_tsep_1 @ B @ ( k1_tsep_1 @ A @ C @ B ) ) & 
% 29.67/29.86                          ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ C @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 29.67/29.86    inference('cnf.neg', [status(esa)], [t46_tmap_1])).
% 29.67/29.86  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf(commutativity_k1_tsep_1, axiom,
% 29.67/29.86    (![A:$i,B:$i,C:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 29.67/29.86         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 29.67/29.86         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86       ( ( k1_tsep_1 @ A @ B @ C ) = ( k1_tsep_1 @ A @ C @ B ) ) ))).
% 29.67/29.86  thf('3', plain,
% 29.67/29.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X4 @ X5)
% 29.67/29.86          | (v2_struct_0 @ X4)
% 29.67/29.86          | ~ (l1_pre_topc @ X5)
% 29.67/29.86          | (v2_struct_0 @ X5)
% 29.67/29.86          | (v2_struct_0 @ X6)
% 29.67/29.86          | ~ (m1_pre_topc @ X6 @ X5)
% 29.67/29.86          | ((k1_tsep_1 @ X5 @ X4 @ X6) = (k1_tsep_1 @ X5 @ X6 @ X4)))),
% 29.67/29.86      inference('cnf', [status(esa)], [commutativity_k1_tsep_1])).
% 29.67/29.86  thf('4', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         (((k1_tsep_1 @ sk_A @ sk_B @ X0) = (k1_tsep_1 @ sk_A @ X0 @ sk_B))
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['2', '3'])).
% 29.67/29.86  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('6', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         (((k1_tsep_1 @ sk_A @ sk_B @ X0) = (k1_tsep_1 @ sk_A @ X0 @ sk_B))
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('demod', [status(thm)], ['4', '5'])).
% 29.67/29.86  thf('7', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_C) = (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['1', '6'])).
% 29.67/29.86  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf(dt_k1_tsep_1, axiom,
% 29.67/29.86    (![A:$i,B:$i,C:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 29.67/29.86         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 29.67/29.86         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 29.67/29.86         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 29.67/29.86         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 29.67/29.86  thf('10', plain,
% 29.67/29.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X7 @ X8)
% 29.67/29.86          | (v2_struct_0 @ X7)
% 29.67/29.86          | ~ (l1_pre_topc @ X8)
% 29.67/29.86          | (v2_struct_0 @ X8)
% 29.67/29.86          | (v2_struct_0 @ X9)
% 29.67/29.86          | ~ (m1_pre_topc @ X9 @ X8)
% 29.67/29.86          | (m1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X9) @ X8))),
% 29.67/29.86      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 29.67/29.86  thf('11', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['9', '10'])).
% 29.67/29.86  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('13', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('demod', [status(thm)], ['11', '12'])).
% 29.67/29.86  thf('14', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['8', '13'])).
% 29.67/29.86  thf(dt_m1_pre_topc, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( l1_pre_topc @ A ) =>
% 29.67/29.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 29.67/29.86  thf('15', plain,
% 29.67/29.86      (![X2 : $i, X3 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 29.67/29.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 29.67/29.86  thf('16', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['14', '15'])).
% 29.67/29.86  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('18', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['16', '17'])).
% 29.67/29.86  thf('19', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['8', '13'])).
% 29.67/29.86  thf(cc1_pre_topc, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 29.67/29.86  thf('20', plain,
% 29.67/29.86      (![X0 : $i, X1 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X0 @ X1)
% 29.67/29.86          | (v2_pre_topc @ X0)
% 29.67/29.86          | ~ (l1_pre_topc @ X1)
% 29.67/29.86          | ~ (v2_pre_topc @ X1))),
% 29.67/29.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 29.67/29.86  thf('21', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | ~ (v2_pre_topc @ sk_A)
% 29.67/29.86        | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['19', '20'])).
% 29.67/29.86  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('24', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['21', '22', '23'])).
% 29.67/29.86  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf(t33_tmap_1, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 29.67/29.86       ( ![B:$i]:
% 29.67/29.86         ( ( ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 29.67/29.86           ( ![C:$i]:
% 29.67/29.86             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 29.67/29.86               ( ![D:$i]:
% 29.67/29.86                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 29.67/29.86                   ( ( m1_pre_topc @ B @ C ) =>
% 29.67/29.86                     ( ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) ) =
% 29.67/29.86                           ( g1_pre_topc @
% 29.67/29.86                             ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 29.67/29.86                         ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 29.67/29.86                           ( g1_pre_topc @
% 29.67/29.86                             ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) | 
% 29.67/29.86                       ( ( ~( r1_tsep_1 @ D @ C ) ) & 
% 29.67/29.86                         ( ~( r1_tsep_1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 29.67/29.86  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 29.67/29.86  thf(zf_stmt_2, axiom,
% 29.67/29.86    (![D:$i,C:$i]:
% 29.67/29.86     ( ( zip_tseitin_1 @ D @ C ) =>
% 29.67/29.86       ( ( ~( r1_tsep_1 @ C @ D ) ) & ( ~( r1_tsep_1 @ D @ C ) ) ) ))).
% 29.67/29.86  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 29.67/29.86  thf(zf_stmt_4, axiom,
% 29.67/29.86    (![D:$i,C:$i,B:$i,A:$i]:
% 29.67/29.86     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 29.67/29.86       ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 29.67/29.86           ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 29.67/29.86         ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) ) =
% 29.67/29.86           ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ))).
% 29.67/29.86  thf(zf_stmt_5, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.86       ( ![B:$i]:
% 29.67/29.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.86           ( ![C:$i]:
% 29.67/29.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86               ( ![D:$i]:
% 29.67/29.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 29.67/29.86                   ( ( m1_pre_topc @ B @ C ) =>
% 29.67/29.86                     ( ( zip_tseitin_1 @ D @ C ) | 
% 29.67/29.86                       ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 29.67/29.86  thf('28', plain,
% 29.67/29.86      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 29.67/29.86         ((v2_struct_0 @ X34)
% 29.67/29.86          | ~ (m1_pre_topc @ X34 @ X35)
% 29.67/29.86          | (v2_struct_0 @ X36)
% 29.67/29.86          | ~ (m1_pre_topc @ X36 @ X35)
% 29.67/29.86          | (zip_tseitin_0 @ X36 @ X37 @ X34 @ X35)
% 29.67/29.86          | (zip_tseitin_1 @ X36 @ X37)
% 29.67/29.86          | ~ (m1_pre_topc @ X34 @ X37)
% 29.67/29.86          | ~ (m1_pre_topc @ X37 @ X35)
% 29.67/29.86          | (v2_struct_0 @ X37)
% 29.67/29.86          | ~ (l1_pre_topc @ X35)
% 29.67/29.86          | ~ (v2_pre_topc @ X35)
% 29.67/29.86          | (v2_struct_0 @ X35))),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.67/29.86  thf('29', plain,
% 29.67/29.86      (![X0 : $i, X1 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_A)
% 29.67/29.86          | ~ (v2_pre_topc @ sk_A)
% 29.67/29.86          | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 29.67/29.86          | (zip_tseitin_1 @ X1 @ X0)
% 29.67/29.86          | (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ X1 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X1)
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['27', '28'])).
% 29.67/29.86  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('32', plain,
% 29.67/29.86      (![X0 : $i, X1 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 29.67/29.86          | (zip_tseitin_1 @ X1 @ X0)
% 29.67/29.86          | (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ X1 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X1)
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('demod', [status(thm)], ['29', '30', '31'])).
% 29.67/29.86  thf('33', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_B)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (zip_tseitin_0 @ X0 @ sk_D @ sk_B @ sk_A)
% 29.67/29.86          | (zip_tseitin_1 @ X0 @ sk_D)
% 29.67/29.86          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 29.67/29.86          | (v2_struct_0 @ sk_D)
% 29.67/29.86          | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['26', '32'])).
% 29.67/29.86  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('35', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_B)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (zip_tseitin_0 @ X0 @ sk_D @ sk_B @ sk_A)
% 29.67/29.86          | (zip_tseitin_1 @ X0 @ sk_D)
% 29.67/29.86          | (v2_struct_0 @ sk_D)
% 29.67/29.86          | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('demod', [status(thm)], ['33', '34'])).
% 29.67/29.86  thf('36', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.86        | (zip_tseitin_0 @ sk_C @ sk_D @ sk_B @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['25', '35'])).
% 29.67/29.86  thf('37', plain,
% 29.67/29.86      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 29.67/29.86         (((k2_tsep_1 @ X29 @ X30 @ (k1_tsep_1 @ X29 @ X28 @ X31))
% 29.67/29.86            = (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 29.67/29.86          | ~ (zip_tseitin_0 @ X31 @ X30 @ X28 @ X29))),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_4])).
% 29.67/29.86  thf('38', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | ((k2_tsep_1 @ sk_A @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 29.67/29.86      inference('sup-', [status(thm)], ['36', '37'])).
% 29.67/29.86  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf(t25_tmap_1, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.86       ( ![B:$i]:
% 29.67/29.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.86           ( ( k1_tsep_1 @ A @ B @ B ) =
% 29.67/29.86             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 29.67/29.86  thf('40', plain,
% 29.67/29.86      (![X22 : $i, X23 : $i]:
% 29.67/29.86         ((v2_struct_0 @ X22)
% 29.67/29.86          | ~ (m1_pre_topc @ X22 @ X23)
% 29.67/29.86          | ((k1_tsep_1 @ X23 @ X22 @ X22)
% 29.67/29.86              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 29.67/29.86          | ~ (l1_pre_topc @ X23)
% 29.67/29.86          | ~ (v2_pre_topc @ X23)
% 29.67/29.86          | (v2_struct_0 @ X23))),
% 29.67/29.86      inference('cnf', [status(esa)], [t25_tmap_1])).
% 29.67/29.86  thf('41', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_D)
% 29.67/29.86        | ~ (v2_pre_topc @ sk_D)
% 29.67/29.86        | ~ (l1_pre_topc @ sk_D)
% 29.67/29.86        | ((k1_tsep_1 @ sk_D @ sk_B @ sk_B)
% 29.67/29.86            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.86        | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['39', '40'])).
% 29.67/29.86  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('43', plain,
% 29.67/29.86      (![X0 : $i, X1 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X0 @ X1)
% 29.67/29.86          | (v2_pre_topc @ X0)
% 29.67/29.86          | ~ (l1_pre_topc @ X1)
% 29.67/29.86          | ~ (v2_pre_topc @ X1))),
% 29.67/29.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 29.67/29.86  thf('44', plain,
% 29.67/29.86      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 29.67/29.86      inference('sup-', [status(thm)], ['42', '43'])).
% 29.67/29.86  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('47', plain, ((v2_pre_topc @ sk_D)),
% 29.67/29.86      inference('demod', [status(thm)], ['44', '45', '46'])).
% 29.67/29.86  thf('48', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('49', plain,
% 29.67/29.86      (![X2 : $i, X3 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 29.67/29.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 29.67/29.86  thf('50', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 29.67/29.86      inference('sup-', [status(thm)], ['48', '49'])).
% 29.67/29.86  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 29.67/29.86      inference('demod', [status(thm)], ['50', '51'])).
% 29.67/29.86  thf('53', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_D)
% 29.67/29.86        | ((k1_tsep_1 @ sk_D @ sk_B @ sk_B)
% 29.67/29.86            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.86        | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('demod', [status(thm)], ['41', '47', '52'])).
% 29.67/29.86  thf('54', plain, (~ (v2_struct_0 @ sk_D)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('55', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | ((k1_tsep_1 @ sk_D @ sk_B @ sk_B)
% 29.67/29.86            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 29.67/29.86      inference('clc', [status(thm)], ['53', '54'])).
% 29.67/29.86  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('57', plain,
% 29.67/29.86      (((k1_tsep_1 @ sk_D @ sk_B @ sk_B)
% 29.67/29.86         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.86      inference('clc', [status(thm)], ['55', '56'])).
% 29.67/29.86  thf('58', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | ((k2_tsep_1 @ sk_A @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86            = (k1_tsep_1 @ sk_D @ sk_B @ sk_B)))),
% 29.67/29.86      inference('demod', [status(thm)], ['38', '57'])).
% 29.67/29.86  thf('59', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('60', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['8', '13'])).
% 29.67/29.86  thf(t44_tmap_1, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.86       ( ![B:$i]:
% 29.67/29.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.86           ( ![C:$i]:
% 29.67/29.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 29.67/29.86                 ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86               ( ( ~( r1_tsep_1 @ C @ B ) ) =>
% 29.67/29.86                 ( ( v1_tsep_1 @ ( k2_tsep_1 @ A @ C @ B ) @ B ) & 
% 29.67/29.86                   ( m1_pre_topc @ ( k2_tsep_1 @ A @ C @ B ) @ B ) ) ) ) ) ) ) ))).
% 29.67/29.86  thf('61', plain,
% 29.67/29.86      (![X42 : $i, X43 : $i, X44 : $i]:
% 29.67/29.86         ((v2_struct_0 @ X42)
% 29.67/29.86          | ~ (m1_pre_topc @ X42 @ X43)
% 29.67/29.86          | (r1_tsep_1 @ X44 @ X42)
% 29.67/29.86          | (v1_tsep_1 @ (k2_tsep_1 @ X43 @ X44 @ X42) @ X42)
% 29.67/29.86          | ~ (m1_pre_topc @ X44 @ X43)
% 29.67/29.86          | ~ (v1_tsep_1 @ X44 @ X43)
% 29.67/29.86          | (v2_struct_0 @ X44)
% 29.67/29.86          | ~ (l1_pre_topc @ X43)
% 29.67/29.86          | ~ (v2_pre_topc @ X43)
% 29.67/29.86          | (v2_struct_0 @ X43))),
% 29.67/29.86      inference('cnf', [status(esa)], [t44_tmap_1])).
% 29.67/29.86  thf('62', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_C)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_B)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | ~ (v2_pre_topc @ sk_A)
% 29.67/29.86          | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (v1_tsep_1 @ 
% 29.67/29.86             (k2_tsep_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 29.67/29.86             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['60', '61'])).
% 29.67/29.86  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('65', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_C)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_B)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (v1_tsep_1 @ 
% 29.67/29.86             (k2_tsep_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 29.67/29.86             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['62', '63', '64'])).
% 29.67/29.86  thf('66', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | (v1_tsep_1 @ 
% 29.67/29.86             (k2_tsep_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 29.67/29.86             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | (v2_struct_0 @ sk_B)
% 29.67/29.86          | (v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ sk_C))),
% 29.67/29.86      inference('simplify', [status(thm)], ['65'])).
% 29.67/29.86  thf('67', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | ~ (v1_tsep_1 @ sk_D @ sk_A)
% 29.67/29.86        | (v1_tsep_1 @ 
% 29.67/29.86           (k2_tsep_1 @ sk_A @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 29.67/29.86           (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['59', '66'])).
% 29.67/29.86  thf('68', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('69', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (v1_tsep_1 @ 
% 29.67/29.86           (k2_tsep_1 @ sk_A @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 29.67/29.86           (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['67', '68'])).
% 29.67/29.86  thf('70', plain,
% 29.67/29.86      (((v1_tsep_1 @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ 
% 29.67/29.86         (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C))),
% 29.67/29.86      inference('sup+', [status(thm)], ['58', '69'])).
% 29.67/29.86  thf('71', plain,
% 29.67/29.86      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_D)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v1_tsep_1 @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ 
% 29.67/29.86           (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('simplify', [status(thm)], ['70'])).
% 29.67/29.86  thf('72', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['21', '22', '23'])).
% 29.67/29.86  thf('73', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['16', '17'])).
% 29.67/29.86  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf(t22_tsep_1, axiom,
% 29.67/29.86    (![A:$i]:
% 29.67/29.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.86       ( ![B:$i]:
% 29.67/29.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.86           ( ![C:$i]:
% 29.67/29.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.86               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 29.67/29.86  thf('76', plain,
% 29.67/29.86      (![X19 : $i, X20 : $i, X21 : $i]:
% 29.67/29.86         ((v2_struct_0 @ X19)
% 29.67/29.86          | ~ (m1_pre_topc @ X19 @ X20)
% 29.67/29.86          | (m1_pre_topc @ X19 @ (k1_tsep_1 @ X20 @ X19 @ X21))
% 29.67/29.86          | ~ (m1_pre_topc @ X21 @ X20)
% 29.67/29.86          | (v2_struct_0 @ X21)
% 29.67/29.86          | ~ (l1_pre_topc @ X20)
% 29.67/29.86          | ~ (v2_pre_topc @ X20)
% 29.67/29.86          | (v2_struct_0 @ X20))),
% 29.67/29.86      inference('cnf', [status(esa)], [t22_tsep_1])).
% 29.67/29.86  thf('77', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_A)
% 29.67/29.86          | ~ (v2_pre_topc @ sk_A)
% 29.67/29.86          | ~ (l1_pre_topc @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['75', '76'])).
% 29.67/29.86  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.86  thf('80', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_A)
% 29.67/29.86          | (v2_struct_0 @ X0)
% 29.67/29.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.86          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 29.67/29.86          | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('demod', [status(thm)], ['77', '78', '79'])).
% 29.67/29.86  thf('81', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['74', '80'])).
% 29.67/29.86  thf('82', plain,
% 29.67/29.86      (![X22 : $i, X23 : $i]:
% 29.67/29.86         ((v2_struct_0 @ X22)
% 29.67/29.86          | ~ (m1_pre_topc @ X22 @ X23)
% 29.67/29.86          | ((k1_tsep_1 @ X23 @ X22 @ X22)
% 29.67/29.86              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 29.67/29.86          | ~ (l1_pre_topc @ X23)
% 29.67/29.86          | ~ (v2_pre_topc @ X23)
% 29.67/29.86          | (v2_struct_0 @ X23))),
% 29.67/29.86      inference('cnf', [status(esa)], [t25_tmap_1])).
% 29.67/29.86  thf('83', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.86        | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('sup-', [status(thm)], ['81', '82'])).
% 29.67/29.86  thf('84', plain,
% 29.67/29.86      ((((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.86        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('simplify', [status(thm)], ['83'])).
% 29.67/29.86  thf('85', plain,
% 29.67/29.86      (((k1_tsep_1 @ sk_D @ sk_B @ sk_B)
% 29.67/29.86         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.86      inference('clc', [status(thm)], ['55', '56'])).
% 29.67/29.86  thf('86', plain,
% 29.67/29.86      ((((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86          = (k1_tsep_1 @ sk_D @ sk_B @ sk_B))
% 29.67/29.86        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('demod', [status(thm)], ['84', '85'])).
% 29.67/29.86  thf('87', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86            = (k1_tsep_1 @ sk_D @ sk_B @ sk_B)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['73', '86'])).
% 29.67/29.86  thf('88', plain,
% 29.67/29.86      ((((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86          = (k1_tsep_1 @ sk_D @ sk_B @ sk_B))
% 29.67/29.86        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('simplify', [status(thm)], ['87'])).
% 29.67/29.86  thf('89', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | ((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86            = (k1_tsep_1 @ sk_D @ sk_B @ sk_B)))),
% 29.67/29.86      inference('sup-', [status(thm)], ['72', '88'])).
% 29.67/29.86  thf('90', plain,
% 29.67/29.86      ((((k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B)
% 29.67/29.86          = (k1_tsep_1 @ sk_D @ sk_B @ sk_B))
% 29.67/29.86        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B))),
% 29.67/29.86      inference('simplify', [status(thm)], ['89'])).
% 29.67/29.86  thf('91', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['74', '80'])).
% 29.67/29.86  thf('92', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A)
% 29.67/29.86        | (v2_struct_0 @ sk_B)
% 29.67/29.86        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.86      inference('demod', [status(thm)], ['16', '17'])).
% 29.67/29.86  thf('93', plain,
% 29.67/29.86      (((v2_struct_0 @ sk_B)
% 29.67/29.86        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.86        | (v2_struct_0 @ sk_C)
% 29.67/29.86        | (v2_struct_0 @ sk_A))),
% 29.67/29.86      inference('sup-', [status(thm)], ['74', '80'])).
% 29.67/29.86  thf('94', plain,
% 29.67/29.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 29.67/29.86         (~ (m1_pre_topc @ X7 @ X8)
% 29.67/29.86          | (v2_struct_0 @ X7)
% 29.67/29.86          | ~ (l1_pre_topc @ X8)
% 29.67/29.86          | (v2_struct_0 @ X8)
% 29.67/29.86          | (v2_struct_0 @ X9)
% 29.67/29.86          | ~ (m1_pre_topc @ X9 @ X8)
% 29.67/29.86          | (m1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X9) @ X8))),
% 29.67/29.86      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 29.67/29.86  thf('95', plain,
% 29.67/29.86      (![X0 : $i]:
% 29.67/29.86         ((v2_struct_0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ sk_C)
% 29.67/29.87          | (v2_struct_0 @ sk_B)
% 29.67/29.87          | (m1_pre_topc @ 
% 29.67/29.87             (k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ X0) @ 
% 29.67/29.87             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['93', '94'])).
% 29.67/29.87  thf('96', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         (~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (m1_pre_topc @ 
% 29.67/29.87             (k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ X0) @ 
% 29.67/29.87             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ sk_B)
% 29.67/29.87          | (v2_struct_0 @ sk_C)
% 29.67/29.87          | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('simplify', [status(thm)], ['95'])).
% 29.67/29.87  thf('97', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         ((v2_struct_0 @ sk_B)
% 29.67/29.87          | (v2_struct_0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ sk_C)
% 29.67/29.87          | (v2_struct_0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ sk_C)
% 29.67/29.87          | (v2_struct_0 @ sk_B)
% 29.67/29.87          | (m1_pre_topc @ 
% 29.67/29.87             (k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ X0) @ 
% 29.67/29.87             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['92', '96'])).
% 29.67/29.87  thf('98', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         ((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (m1_pre_topc @ 
% 29.67/29.87             (k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ X0) @ 
% 29.67/29.87             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87          | (v2_struct_0 @ sk_C)
% 29.67/29.87          | (v2_struct_0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('simplify', [status(thm)], ['97'])).
% 29.67/29.87  thf('99', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (m1_pre_topc @ 
% 29.67/29.87           (k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B) @ 
% 29.67/29.87           (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['91', '98'])).
% 29.67/29.87  thf('100', plain,
% 29.67/29.87      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (m1_pre_topc @ 
% 29.67/29.87           (k1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ sk_B) @ 
% 29.67/29.87           (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('simplify', [status(thm)], ['99'])).
% 29.67/29.87  thf('101', plain,
% 29.67/29.87      (((m1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ 
% 29.67/29.87         (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup+', [status(thm)], ['90', '100'])).
% 29.67/29.87  thf('102', plain,
% 29.67/29.87      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (m1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ 
% 29.67/29.87           (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('simplify', [status(thm)], ['101'])).
% 29.67/29.87  thf('103', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('104', plain,
% 29.67/29.87      (![X22 : $i, X23 : $i]:
% 29.67/29.87         ((v2_struct_0 @ X22)
% 29.67/29.87          | ~ (m1_pre_topc @ X22 @ X23)
% 29.67/29.87          | ((k1_tsep_1 @ X23 @ X22 @ X22)
% 29.67/29.87              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 29.67/29.87          | ~ (l1_pre_topc @ X23)
% 29.67/29.87          | ~ (v2_pre_topc @ X23)
% 29.67/29.87          | (v2_struct_0 @ X23))),
% 29.67/29.87      inference('cnf', [status(esa)], [t25_tmap_1])).
% 29.67/29.87  thf('105', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_A)
% 29.67/29.87        | ~ (v2_pre_topc @ sk_A)
% 29.67/29.87        | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['103', '104'])).
% 29.67/29.87  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('108', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_A)
% 29.67/29.87        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)], ['105', '106', '107'])).
% 29.67/29.87  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('110', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 29.67/29.87      inference('clc', [status(thm)], ['108', '109'])).
% 29.67/29.87  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('112', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.87      inference('clc', [status(thm)], ['110', '111'])).
% 29.67/29.87  thf(t14_tmap_1, axiom,
% 29.67/29.87    (![A:$i]:
% 29.67/29.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.87       ( ![B:$i]:
% 29.67/29.87         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 29.67/29.87           ( ![C:$i]:
% 29.67/29.87             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 29.67/29.87               ( ( ( C ) =
% 29.67/29.87                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 29.67/29.87                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 29.67/29.87                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 29.67/29.87  thf('113', plain,
% 29.67/29.87      (![X13 : $i, X14 : $i, X15 : $i]:
% 29.67/29.87         (~ (v2_pre_topc @ X13)
% 29.67/29.87          | ~ (l1_pre_topc @ X13)
% 29.67/29.87          | ((X14) != (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 29.67/29.87          | ~ (v1_tsep_1 @ X14 @ X15)
% 29.67/29.87          | ~ (m1_pre_topc @ X14 @ X15)
% 29.67/29.87          | (v1_tsep_1 @ X13 @ X15)
% 29.67/29.87          | ~ (l1_pre_topc @ X14)
% 29.67/29.87          | ~ (v2_pre_topc @ X14)
% 29.67/29.87          | ~ (l1_pre_topc @ X15)
% 29.67/29.87          | ~ (v2_pre_topc @ X15))),
% 29.67/29.87      inference('cnf', [status(esa)], [t14_tmap_1])).
% 29.67/29.87  thf('114', plain,
% 29.67/29.87      (![X13 : $i, X15 : $i]:
% 29.67/29.87         (~ (v2_pre_topc @ X15)
% 29.67/29.87          | ~ (l1_pre_topc @ X15)
% 29.67/29.87          | ~ (v2_pre_topc @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 29.67/29.87          | ~ (l1_pre_topc @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 29.67/29.87          | (v1_tsep_1 @ X13 @ X15)
% 29.67/29.87          | ~ (m1_pre_topc @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)) @ X15)
% 29.67/29.87          | ~ (v1_tsep_1 @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)) @ X15)
% 29.67/29.87          | ~ (l1_pre_topc @ X13)
% 29.67/29.87          | ~ (v2_pre_topc @ X13))),
% 29.67/29.87      inference('simplify', [status(thm)], ['113'])).
% 29.67/29.87  thf('115', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 29.67/29.87          | ~ (v2_pre_topc @ sk_B)
% 29.67/29.87          | ~ (l1_pre_topc @ sk_B)
% 29.67/29.87          | ~ (v1_tsep_1 @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 29.67/29.87          | (v1_tsep_1 @ sk_B @ X0)
% 29.67/29.87          | ~ (l1_pre_topc @ 
% 29.67/29.87               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 29.67/29.87          | ~ (l1_pre_topc @ X0)
% 29.67/29.87          | ~ (v2_pre_topc @ X0))),
% 29.67/29.87      inference('sup-', [status(thm)], ['112', '114'])).
% 29.67/29.87  thf('116', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('117', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | (v2_struct_0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)], ['11', '12'])).
% 29.67/29.87  thf('118', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ sk_A))),
% 29.67/29.87      inference('sup-', [status(thm)], ['116', '117'])).
% 29.67/29.87  thf('119', plain,
% 29.67/29.87      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('simplify', [status(thm)], ['118'])).
% 29.67/29.87  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('121', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ sk_A))),
% 29.67/29.87      inference('clc', [status(thm)], ['119', '120'])).
% 29.67/29.87  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('123', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ sk_A)),
% 29.67/29.87      inference('clc', [status(thm)], ['121', '122'])).
% 29.67/29.87  thf('124', plain,
% 29.67/29.87      (![X0 : $i, X1 : $i]:
% 29.67/29.87         (~ (m1_pre_topc @ X0 @ X1)
% 29.67/29.87          | (v2_pre_topc @ X0)
% 29.67/29.87          | ~ (l1_pre_topc @ X1)
% 29.67/29.87          | ~ (v2_pre_topc @ X1))),
% 29.67/29.87      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 29.67/29.87  thf('125', plain,
% 29.67/29.87      ((~ (v2_pre_topc @ sk_A)
% 29.67/29.87        | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['123', '124'])).
% 29.67/29.87  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('128', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)], ['125', '126', '127'])).
% 29.67/29.87  thf('129', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('130', plain,
% 29.67/29.87      (![X0 : $i, X1 : $i]:
% 29.67/29.87         (~ (m1_pre_topc @ X0 @ X1)
% 29.67/29.87          | (v2_pre_topc @ X0)
% 29.67/29.87          | ~ (l1_pre_topc @ X1)
% 29.67/29.87          | ~ (v2_pre_topc @ X1))),
% 29.67/29.87      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 29.67/29.87  thf('131', plain,
% 29.67/29.87      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['129', '130'])).
% 29.67/29.87  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 29.67/29.87      inference('demod', [status(thm)], ['131', '132', '133'])).
% 29.67/29.87  thf('135', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('136', plain,
% 29.67/29.87      (![X2 : $i, X3 : $i]:
% 29.67/29.87         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 29.67/29.87      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 29.67/29.87  thf('137', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['135', '136'])).
% 29.67/29.87  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 29.67/29.87      inference('demod', [status(thm)], ['137', '138'])).
% 29.67/29.87  thf('140', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.87      inference('clc', [status(thm)], ['110', '111'])).
% 29.67/29.87  thf('141', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.87      inference('clc', [status(thm)], ['110', '111'])).
% 29.67/29.87  thf('142', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.87      inference('clc', [status(thm)], ['110', '111'])).
% 29.67/29.87  thf('143', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ sk_A)),
% 29.67/29.87      inference('clc', [status(thm)], ['121', '122'])).
% 29.67/29.87  thf('144', plain,
% 29.67/29.87      (![X2 : $i, X3 : $i]:
% 29.67/29.87         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 29.67/29.87      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 29.67/29.87  thf('145', plain,
% 29.67/29.87      ((~ (l1_pre_topc @ sk_A)
% 29.67/29.87        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['143', '144'])).
% 29.67/29.87  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('147', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)], ['145', '146'])).
% 29.67/29.87  thf('148', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         (~ (v1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B) @ X0)
% 29.67/29.87          | (v1_tsep_1 @ sk_B @ X0)
% 29.67/29.87          | ~ (l1_pre_topc @ X0)
% 29.67/29.87          | ~ (v2_pre_topc @ X0))),
% 29.67/29.87      inference('demod', [status(thm)],
% 29.67/29.87                ['115', '128', '134', '139', '140', '141', '142', '147'])).
% 29.67/29.87  thf('149', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_D @ sk_B @ sk_B)
% 29.67/29.87         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.87      inference('clc', [status(thm)], ['55', '56'])).
% 29.67/29.87  thf('150', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 29.67/29.87         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 29.67/29.87      inference('clc', [status(thm)], ['110', '111'])).
% 29.67/29.87  thf('151', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B) = (k1_tsep_1 @ sk_D @ sk_B @ sk_B))),
% 29.67/29.87      inference('sup+', [status(thm)], ['149', '150'])).
% 29.67/29.87  thf('152', plain,
% 29.67/29.87      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B) = (k1_tsep_1 @ sk_D @ sk_B @ sk_B))),
% 29.67/29.87      inference('sup+', [status(thm)], ['149', '150'])).
% 29.67/29.87  thf('153', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         (~ (v1_tsep_1 @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ X0)
% 29.67/29.87          | (v1_tsep_1 @ sk_B @ X0)
% 29.67/29.87          | ~ (l1_pre_topc @ X0)
% 29.67/29.87          | ~ (v2_pre_topc @ X0))),
% 29.67/29.87      inference('demod', [status(thm)], ['148', '151', '152'])).
% 29.67/29.87  thf('154', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (v1_tsep_1 @ (k1_tsep_1 @ sk_D @ sk_B @ sk_B) @ 
% 29.67/29.87             (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['102', '153'])).
% 29.67/29.87  thf('155', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['71', '154'])).
% 29.67/29.87  thf('156', plain,
% 29.67/29.87      ((~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('simplify', [status(thm)], ['155'])).
% 29.67/29.87  thf('157', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['24', '156'])).
% 29.67/29.87  thf('158', plain,
% 29.67/29.87      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('simplify', [status(thm)], ['157'])).
% 29.67/29.87  thf('159', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['18', '158'])).
% 29.67/29.87  thf('160', plain,
% 29.67/29.87      (((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('simplify', [status(thm)], ['159'])).
% 29.67/29.87  thf('161', plain,
% 29.67/29.87      (((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup+', [status(thm)], ['7', '160'])).
% 29.67/29.87  thf('162', plain,
% 29.67/29.87      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('simplify', [status(thm)], ['161'])).
% 29.67/29.87  thf('163', plain,
% 29.67/29.87      ((~ (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | ~ (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))
% 29.67/29.87        | ~ (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('164', plain,
% 29.67/29.87      ((~ (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))))),
% 29.67/29.87      inference('split', [status(esa)], ['163'])).
% 29.67/29.87  thf('165', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_C) = (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['1', '6'])).
% 29.67/29.87  thf('166', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('sup-', [status(thm)], ['74', '80'])).
% 29.67/29.87  thf('167', plain,
% 29.67/29.87      (((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup+', [status(thm)], ['165', '166'])).
% 29.67/29.87  thf('168', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('simplify', [status(thm)], ['167'])).
% 29.67/29.87  thf('169', plain,
% 29.67/29.87      ((~ (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))))),
% 29.67/29.87      inference('split', [status(esa)], ['163'])).
% 29.67/29.87  thf('170', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['168', '169'])).
% 29.67/29.87  thf('171', plain, (~ (v2_struct_0 @ sk_C)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('172', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))))),
% 29.67/29.87      inference('clc', [status(thm)], ['170', '171'])).
% 29.67/29.87  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('174', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_A))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))))),
% 29.67/29.87      inference('clc', [status(thm)], ['172', '173'])).
% 29.67/29.87  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('176', plain,
% 29.67/29.87      (((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['174', '175'])).
% 29.67/29.87  thf('177', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('sup-', [status(thm)], ['74', '80'])).
% 29.67/29.87  thf('178', plain,
% 29.67/29.87      ((~ (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('split', [status(esa)], ['163'])).
% 29.67/29.87  thf('179', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['177', '178'])).
% 29.67/29.87  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('181', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('clc', [status(thm)], ['179', '180'])).
% 29.67/29.87  thf('182', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('183', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_C))
% 29.67/29.87         <= (~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('clc', [status(thm)], ['181', '182'])).
% 29.67/29.87  thf('184', plain, (~ (v2_struct_0 @ sk_C)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('185', plain,
% 29.67/29.87      (((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['183', '184'])).
% 29.67/29.87  thf('186', plain,
% 29.67/29.87      (((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('simplify', [status(thm)], ['159'])).
% 29.67/29.87  thf('187', plain,
% 29.67/29.87      ((~ (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('split', [status(esa)], ['163'])).
% 29.67/29.87  thf('188', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['186', '187'])).
% 29.67/29.87  thf(t39_tmap_1, axiom,
% 29.67/29.87    (![A:$i]:
% 29.67/29.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.87       ( ![B:$i]:
% 29.67/29.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.87           ( ![C:$i]:
% 29.67/29.87             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.87               ( ![D:$i]:
% 29.67/29.87                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 29.67/29.87                   ( ( ~( ( ~( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 29.67/29.87                          ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 29.67/29.87                     ( ~( ( ~( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 29.67/29.87                          ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) ) & 
% 29.67/29.87                     ( ~( ( ~( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 29.67/29.87                          ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 29.67/29.87                     ( ~( ( ~( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 29.67/29.87                          ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 29.67/29.87  thf('189', plain,
% 29.67/29.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.67/29.87         ((v2_struct_0 @ X38)
% 29.67/29.87          | ~ (m1_pre_topc @ X38 @ X39)
% 29.67/29.87          | (v2_struct_0 @ X40)
% 29.67/29.87          | ~ (m1_pre_topc @ X40 @ X39)
% 29.67/29.87          | ~ (r1_tsep_1 @ X40 @ (k1_tsep_1 @ X39 @ X38 @ X41))
% 29.67/29.87          | (r1_tsep_1 @ X40 @ X38)
% 29.67/29.87          | ~ (m1_pre_topc @ X41 @ X39)
% 29.67/29.87          | (v2_struct_0 @ X41)
% 29.67/29.87          | ~ (l1_pre_topc @ X39)
% 29.67/29.87          | ~ (v2_pre_topc @ X39)
% 29.67/29.87          | (v2_struct_0 @ X39))),
% 29.67/29.87      inference('cnf', [status(esa)], [t39_tmap_1])).
% 29.67/29.87  thf('190', plain,
% 29.67/29.87      ((((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87         | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | ~ (v2_pre_topc @ sk_A)
% 29.67/29.87         | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 29.67/29.87         | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['188', '189'])).
% 29.67/29.87  thf('191', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('193', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('194', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('195', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('196', plain,
% 29.67/29.87      ((((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87         | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('demod', [status(thm)],
% 29.67/29.87                ['190', '191', '192', '193', '194', '195'])).
% 29.67/29.87  thf('197', plain,
% 29.67/29.87      ((((r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('simplify', [status(thm)], ['196'])).
% 29.67/29.87  thf('198', plain,
% 29.67/29.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 29.67/29.87         (~ (m1_pre_topc @ X7 @ X8)
% 29.67/29.87          | (v2_struct_0 @ X7)
% 29.67/29.87          | ~ (l1_pre_topc @ X8)
% 29.67/29.87          | (v2_struct_0 @ X8)
% 29.67/29.87          | (v2_struct_0 @ X9)
% 29.67/29.87          | ~ (m1_pre_topc @ X9 @ X8)
% 29.67/29.87          | ~ (v2_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X9)))),
% 29.67/29.87      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 29.67/29.87  thf('199', plain,
% 29.67/29.87      ((((zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['197', '198'])).
% 29.67/29.87  thf('200', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('202', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('203', plain,
% 29.67/29.87      ((((zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('demod', [status(thm)], ['199', '200', '201', '202'])).
% 29.67/29.87  thf('204', plain,
% 29.67/29.87      ((((r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (zip_tseitin_1 @ sk_C @ sk_D)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('simplify', [status(thm)], ['203'])).
% 29.67/29.87  thf('205', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('206', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf(t22_tmap_1, axiom,
% 29.67/29.87    (![A:$i]:
% 29.67/29.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.67/29.87       ( ![B:$i]:
% 29.67/29.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 29.67/29.87           ( ![C:$i]:
% 29.67/29.87             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 29.67/29.87               ( ( m1_pre_topc @ B @ C ) =>
% 29.67/29.87                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 29.67/29.87  thf('207', plain,
% 29.67/29.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 29.67/29.87         ((v2_struct_0 @ X16)
% 29.67/29.87          | ~ (m1_pre_topc @ X16 @ X17)
% 29.67/29.87          | ~ (m1_pre_topc @ X16 @ X18)
% 29.67/29.87          | ~ (r1_tsep_1 @ X18 @ X16)
% 29.67/29.87          | ~ (m1_pre_topc @ X18 @ X17)
% 29.67/29.87          | (v2_struct_0 @ X18)
% 29.67/29.87          | ~ (l1_pre_topc @ X17)
% 29.67/29.87          | ~ (v2_pre_topc @ X17)
% 29.67/29.87          | (v2_struct_0 @ X17))),
% 29.67/29.87      inference('cnf', [status(esa)], [t22_tmap_1])).
% 29.67/29.87  thf('208', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         ((v2_struct_0 @ sk_A)
% 29.67/29.87          | ~ (v2_pre_topc @ sk_A)
% 29.67/29.87          | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.87          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 29.67/29.87          | ~ (m1_pre_topc @ sk_B @ X0)
% 29.67/29.87          | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['206', '207'])).
% 29.67/29.87  thf('209', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('211', plain,
% 29.67/29.87      (![X0 : $i]:
% 29.67/29.87         ((v2_struct_0 @ sk_A)
% 29.67/29.87          | (v2_struct_0 @ X0)
% 29.67/29.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 29.67/29.87          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 29.67/29.87          | ~ (m1_pre_topc @ sk_B @ X0)
% 29.67/29.87          | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)], ['208', '209', '210'])).
% 29.67/29.87  thf('212', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | ~ (m1_pre_topc @ sk_B @ sk_D)
% 29.67/29.87        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('sup-', [status(thm)], ['205', '211'])).
% 29.67/29.87  thf('213', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('214', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('demod', [status(thm)], ['212', '213'])).
% 29.67/29.87  thf('215', plain,
% 29.67/29.87      ((((zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['204', '214'])).
% 29.67/29.87  thf('216', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_B)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_D)
% 29.67/29.87         | (zip_tseitin_1 @ sk_C @ sk_D)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('simplify', [status(thm)], ['215'])).
% 29.67/29.87  thf('217', plain, ((r1_tsep_1 @ sk_D @ sk_C)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('218', plain,
% 29.67/29.87      (![X32 : $i, X33 : $i]:
% 29.67/29.87         (~ (r1_tsep_1 @ X32 @ X33) | ~ (zip_tseitin_1 @ X33 @ X32))),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 29.67/29.87  thf('219', plain, (~ (zip_tseitin_1 @ sk_C @ sk_D)),
% 29.67/29.87      inference('sup-', [status(thm)], ['217', '218'])).
% 29.67/29.87  thf('220', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_D)
% 29.67/29.87         | (v2_struct_0 @ sk_C)
% 29.67/29.87         | (v2_struct_0 @ sk_A)
% 29.67/29.87         | (v2_struct_0 @ sk_B)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['216', '219'])).
% 29.67/29.87  thf('221', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('222', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('sup-', [status(thm)], ['220', '221'])).
% 29.67/29.87  thf('223', plain, (~ (v2_struct_0 @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('224', plain,
% 29.67/29.87      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('clc', [status(thm)], ['222', '223'])).
% 29.67/29.87  thf('225', plain, (~ (v2_struct_0 @ sk_D)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('226', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_C))
% 29.67/29.87         <= (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 29.67/29.87      inference('clc', [status(thm)], ['224', '225'])).
% 29.67/29.87  thf('227', plain, (~ (v2_struct_0 @ sk_C)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('228', plain, (((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['226', '227'])).
% 29.67/29.87  thf('229', plain,
% 29.67/29.87      (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))) | 
% 29.67/29.87       ~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 29.67/29.87       ~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 29.67/29.87       ~ ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('split', [status(esa)], ['163'])).
% 29.67/29.87  thf('230', plain,
% 29.67/29.87      (~ ((v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 29.67/29.87      inference('sat_resolution*', [status(thm)], ['176', '185', '228', '229'])).
% 29.67/29.87  thf('231', plain, (~ (v1_tsep_1 @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_B))),
% 29.67/29.87      inference('simpl_trail', [status(thm)], ['164', '230'])).
% 29.67/29.87  thf('232', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('sup-', [status(thm)], ['162', '231'])).
% 29.67/29.87  thf('233', plain,
% 29.67/29.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 29.67/29.87         ((v2_struct_0 @ X38)
% 29.67/29.87          | ~ (m1_pre_topc @ X38 @ X39)
% 29.67/29.87          | (v2_struct_0 @ X40)
% 29.67/29.87          | ~ (m1_pre_topc @ X40 @ X39)
% 29.67/29.87          | ~ (r1_tsep_1 @ X40 @ (k1_tsep_1 @ X39 @ X38 @ X41))
% 29.67/29.87          | (r1_tsep_1 @ X40 @ X38)
% 29.67/29.87          | ~ (m1_pre_topc @ X41 @ X39)
% 29.67/29.87          | (v2_struct_0 @ X41)
% 29.67/29.87          | ~ (l1_pre_topc @ X39)
% 29.67/29.87          | ~ (v2_pre_topc @ X39)
% 29.67/29.87          | (v2_struct_0 @ X39))),
% 29.67/29.87      inference('cnf', [status(esa)], [t39_tmap_1])).
% 29.67/29.87  thf('234', plain,
% 29.67/29.87      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | ~ (v2_pre_topc @ sk_A)
% 29.67/29.87        | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['232', '233'])).
% 29.67/29.87  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('237', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('238', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('239', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('240', plain,
% 29.67/29.87      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)],
% 29.67/29.87                ['234', '235', '236', '237', '238', '239'])).
% 29.67/29.87  thf('241', plain,
% 29.67/29.87      (((r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 29.67/29.87      inference('simplify', [status(thm)], ['240'])).
% 29.67/29.87  thf('242', plain,
% 29.67/29.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 29.67/29.87         (~ (m1_pre_topc @ X7 @ X8)
% 29.67/29.87          | (v2_struct_0 @ X7)
% 29.67/29.87          | ~ (l1_pre_topc @ X8)
% 29.67/29.87          | (v2_struct_0 @ X8)
% 29.67/29.87          | (v2_struct_0 @ X9)
% 29.67/29.87          | ~ (m1_pre_topc @ X9 @ X8)
% 29.67/29.87          | ~ (v2_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X9)))),
% 29.67/29.87      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 29.67/29.87  thf('243', plain,
% 29.67/29.87      (((zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | ~ (l1_pre_topc @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 29.67/29.87      inference('sup-', [status(thm)], ['241', '242'])).
% 29.67/29.87  thf('244', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('245', plain, ((l1_pre_topc @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('246', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('247', plain,
% 29.67/29.87      (((zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('demod', [status(thm)], ['243', '244', '245', '246'])).
% 29.67/29.87  thf('248', plain,
% 29.67/29.87      (((r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D))),
% 29.67/29.87      inference('simplify', [status(thm)], ['247'])).
% 29.67/29.87  thf('249', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_B)
% 29.67/29.87        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('demod', [status(thm)], ['212', '213'])).
% 29.67/29.87  thf('250', plain,
% 29.67/29.87      (((zip_tseitin_1 @ sk_C @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B))),
% 29.67/29.87      inference('sup-', [status(thm)], ['248', '249'])).
% 29.67/29.87  thf('251', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_C)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_D)
% 29.67/29.87        | (zip_tseitin_1 @ sk_C @ sk_D))),
% 29.67/29.87      inference('simplify', [status(thm)], ['250'])).
% 29.67/29.87  thf('252', plain, (~ (zip_tseitin_1 @ sk_C @ sk_D)),
% 29.67/29.87      inference('sup-', [status(thm)], ['217', '218'])).
% 29.67/29.87  thf('253', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_D)
% 29.67/29.87        | (v2_struct_0 @ sk_B)
% 29.67/29.87        | (v2_struct_0 @ sk_A)
% 29.67/29.87        | (v2_struct_0 @ sk_C))),
% 29.67/29.87      inference('sup-', [status(thm)], ['251', '252'])).
% 29.67/29.87  thf('254', plain, (~ (v2_struct_0 @ sk_B)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('255', plain,
% 29.67/29.87      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 29.67/29.87      inference('sup-', [status(thm)], ['253', '254'])).
% 29.67/29.87  thf('256', plain, (~ (v2_struct_0 @ sk_C)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('257', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 29.67/29.87      inference('clc', [status(thm)], ['255', '256'])).
% 29.67/29.87  thf('258', plain, (~ (v2_struct_0 @ sk_D)),
% 29.67/29.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.67/29.87  thf('259', plain, ((v2_struct_0 @ sk_A)),
% 29.67/29.87      inference('clc', [status(thm)], ['257', '258'])).
% 29.67/29.87  thf('260', plain, ($false), inference('demod', [status(thm)], ['0', '259'])).
% 29.67/29.87  
% 29.67/29.87  % SZS output end Refutation
% 29.67/29.87  
% 29.67/29.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
