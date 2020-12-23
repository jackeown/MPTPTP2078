%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7uBLHgetvQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:32 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 803 expanded)
%              Number of leaves         :   37 ( 230 expanded)
%              Depth                    :   49
%              Number of atoms          : 2760 (24904 expanded)
%              Number of equality atoms :   77 ( 822 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t33_tmap_1,conjecture,(
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
                      | ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) )).

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
                        | ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
                            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                          & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) )
                            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tsep_1,axiom,(
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
               => ( ( ( m1_pre_topc @ B @ C )
                   => ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                  & ( ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( m1_pre_topc @ B @ C ) )
                  & ( ( m1_pre_topc @ C @ B )
                   => ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) )
                  & ( ( ( k2_tsep_1 @ A @ B @ C )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                   => ( m1_pre_topc @ C @ B ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tsep_1 @ X23 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( ( k2_tsep_1 @ X24 @ X23 @ X25 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k2_tsep_1 @ sk_A @ sk_C @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
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
      | ( ( k2_tsep_1 @ sk_A @ sk_C @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf(t31_tmap_1,axiom,(
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
                 => ( ~ ( ~ ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
                              = ( k2_tsep_1 @ A @ C @ B ) )
                            & ( ( k2_tsep_1 @ A @ ( k1_tsep_1 @ A @ B @ D ) @ C )
                              = ( k2_tsep_1 @ A @ B @ C ) ) )
                        & ( ( r1_tsep_1 @ C @ D )
                          | ( r1_tsep_1 @ D @ C ) )
                        & ~ ( ( r1_tsep_1 @ C @ B )
                            & ( r1_tsep_1 @ B @ C ) ) )
                    & ~ ( ~ ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
                              = ( k2_tsep_1 @ A @ C @ D ) )
                            & ( ( k2_tsep_1 @ A @ ( k1_tsep_1 @ A @ B @ D ) @ C )
                              = ( k2_tsep_1 @ A @ D @ C ) ) )
                        & ~ ( ( r1_tsep_1 @ C @ D )
                            & ( r1_tsep_1 @ D @ C ) )
                        & ( ( r1_tsep_1 @ C @ B )
                          | ( r1_tsep_1 @ B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i] :
      ( ( ( r1_tsep_1 @ B @ C )
        | ( r1_tsep_1 @ C @ B ) )
     => ( zip_tseitin_5 @ C @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_5 @ X17 @ X18 )
      | ~ ( r1_tsep_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ( zip_tseitin_5 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_4 @ D @ C )
     => ( ( r1_tsep_1 @ D @ C )
        & ( r1_tsep_1 @ C @ D ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
     => ( ( ( k2_tsep_1 @ A @ ( k1_tsep_1 @ A @ B @ D ) @ C )
          = ( k2_tsep_1 @ A @ D @ C ) )
        & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
          = ( k2_tsep_1 @ A @ C @ D ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_2 @ C @ B )
     => ( ( r1_tsep_1 @ B @ C )
        & ( r1_tsep_1 @ C @ B ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [D: $i,C: $i] :
      ( ( ( r1_tsep_1 @ D @ C )
        | ( r1_tsep_1 @ C @ D ) )
     => ( zip_tseitin_1 @ D @ C ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( ( k2_tsep_1 @ A @ ( k1_tsep_1 @ A @ B @ D ) @ C )
          = ( k2_tsep_1 @ A @ B @ C ) )
        & ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) )
          = ( k2_tsep_1 @ A @ C @ B ) ) ) ) )).

thf(zf_stmt_13,axiom,(
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
                 => ( ~ ( ( zip_tseitin_5 @ C @ B )
                        & ~ ( zip_tseitin_4 @ D @ C )
                        & ~ ( zip_tseitin_3 @ D @ C @ B @ A ) )
                    & ~ ( ~ ( zip_tseitin_2 @ C @ B )
                        & ( zip_tseitin_1 @ D @ C )
                        & ~ ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( zip_tseitin_3 @ X21 @ X22 @ X19 @ X20 )
      | ( zip_tseitin_4 @ X21 @ X22 )
      | ~ ( zip_tseitin_5 @ X22 @ X19 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( zip_tseitin_5 @ X0 @ sk_D )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 @ sk_D @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
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
      | ~ ( zip_tseitin_5 @ X0 @ sk_D )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 @ sk_D @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_C )
      | ~ ( zip_tseitin_5 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( zip_tseitin_4 @ X0 @ sk_C )
        | ( zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_3 @ sk_B @ sk_C @ sk_D @ sk_A )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_5 @ X17 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ( zip_tseitin_5 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_C )
      | ~ ( zip_tseitin_5 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( zip_tseitin_4 @ X0 @ sk_C )
        | ( zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_3 @ sk_B @ sk_C @ sk_D @ sk_A )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_tsep_1 @ X11 @ X13 @ ( k1_tsep_1 @ X11 @ X14 @ X12 ) )
        = ( k2_tsep_1 @ X11 @ X13 @ X12 ) )
      | ~ ( zip_tseitin_3 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
        = ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('39',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 )
      | ~ ( r1_tsep_1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( zip_tseitin_0 @ X21 @ X22 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X22 )
      | ( zip_tseitin_2 @ X22 @ X19 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B )
      | ~ ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ X0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C )
    | ( zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_tsep_1 @ X3 @ X5 @ ( k1_tsep_1 @ X3 @ X4 @ X6 ) )
        = ( k2_tsep_1 @ X3 @ X5 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
        = ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('56',plain,
    ( ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
       != ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( r1_tsep_1 @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tsep_1 @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( r1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('95',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 )
      | ~ ( r1_tsep_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_2 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C )
    | ( zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_tsep_1 @ X3 @ X5 @ ( k1_tsep_1 @ X3 @ X4 @ X6 ) )
        = ( k2_tsep_1 @ X3 @ X5 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
        = ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('102',plain,
    ( ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
       != ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_2 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tsep_1 @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('122',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('123',plain,(
    ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['92','120','121','122'])).

thf('124',plain,(
    ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['37','123'])).

thf('125',plain,
    ( ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['35','124'])).

thf('126',plain,
    ( ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
       != ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['26','125'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( zip_tseitin_4 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tsep_1 @ X15 @ X16 )
      | ~ ( zip_tseitin_4 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    r1_tsep_1 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['143','121'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_3 @ sk_B @ sk_C @ sk_D @ sk_A )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['25','144'])).

thf('146',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_tsep_1 @ X11 @ X13 @ ( k1_tsep_1 @ X11 @ X14 @ X12 ) )
        = ( k2_tsep_1 @ X11 @ X13 @ X12 ) )
      | ~ ( zip_tseitin_3 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      = ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ( k2_tsep_1 @ sk_A @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['37','123'])).

thf('149',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k2_tsep_1 @ sk_A @ sk_C @ sk_B )
     != ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_4 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tsep_1 @ X15 @ X16 )
      | ~ ( zip_tseitin_4 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['0','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7uBLHgetvQ
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 352 iterations in 0.193s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.64  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.46/0.64  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.46/0.64  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(t33_tmap_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.64               ( ![D:$i]:
% 0.46/0.64                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.46/0.64                   ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.64                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.46/0.64                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.46/0.64                       ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 0.46/0.64                           ( g1_pre_topc @
% 0.46/0.64                             ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.46/0.64                         ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) ) =
% 0.46/0.64                           ( g1_pre_topc @
% 0.46/0.64                             ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.64            ( l1_pre_topc @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.64                  ( ![D:$i]:
% 0.46/0.64                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.46/0.64                      ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.64                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.46/0.64                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.46/0.64                          ( ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 0.46/0.64                              ( g1_pre_topc @
% 0.46/0.64                                ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.46/0.64                            ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ D @ B ) ) =
% 0.46/0.64                              ( g1_pre_topc @
% 0.46/0.64                                ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t33_tmap_1])).
% 0.46/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t31_tsep_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.64               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.46/0.64                 ( ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.64                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.46/0.64                       ( g1_pre_topc @
% 0.46/0.64                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.46/0.64                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.46/0.64                       ( g1_pre_topc @
% 0.46/0.64                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.64                     ( m1_pre_topc @ B @ C ) ) & 
% 0.46/0.64                   ( ( m1_pre_topc @ C @ B ) =>
% 0.46/0.64                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.46/0.64                       ( g1_pre_topc @
% 0.46/0.64                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) & 
% 0.46/0.64                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 0.46/0.64                       ( g1_pre_topc @
% 0.46/0.64                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.46/0.64                     ( m1_pre_topc @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X23)
% 0.46/0.64          | ~ (m1_pre_topc @ X23 @ X24)
% 0.46/0.64          | (r1_tsep_1 @ X23 @ X25)
% 0.46/0.64          | ~ (m1_pre_topc @ X25 @ X23)
% 0.46/0.64          | ((k2_tsep_1 @ X24 @ X23 @ X25)
% 0.46/0.64              = (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 0.46/0.64          | ~ (m1_pre_topc @ X25 @ X24)
% 0.46/0.64          | (v2_struct_0 @ X25)
% 0.46/0.64          | ~ (l1_pre_topc @ X24)
% 0.46/0.64          | ~ (v2_pre_topc @ X24)
% 0.46/0.64          | (v2_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_tsep_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ((k2_tsep_1 @ sk_A @ sk_C @ X0)
% 0.46/0.64              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.46/0.64          | (r1_tsep_1 @ sk_C @ X0)
% 0.46/0.64          | (v2_struct_0 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ((k2_tsep_1 @ sk_A @ sk_C @ X0)
% 0.46/0.64              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.46/0.64          | (r1_tsep_1 @ sk_C @ X0)
% 0.46/0.64          | (v2_struct_0 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '7'])).
% 0.46/0.64  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('12', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('split', [status(esa)], ['12'])).
% 0.46/0.64  thf(t31_tmap_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 0.46/0.64               ( ![D:$i]:
% 0.46/0.64                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 0.46/0.64                   ( ( ~( ( ~( ( ( k2_tsep_1 @
% 0.46/0.64                                   A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 0.46/0.64                                 ( k2_tsep_1 @ A @ C @ B ) ) & 
% 0.46/0.64                               ( ( k2_tsep_1 @
% 0.46/0.64                                   A @ ( k1_tsep_1 @ A @ B @ D ) @ C ) =
% 0.46/0.64                                 ( k2_tsep_1 @ A @ B @ C ) ) ) ) & 
% 0.46/0.64                          ( ( r1_tsep_1 @ C @ D ) | ( r1_tsep_1 @ D @ C ) ) & 
% 0.46/0.64                          ( ~( ( r1_tsep_1 @ C @ B ) & ( r1_tsep_1 @ B @ C ) ) ) ) ) & 
% 0.46/0.64                     ( ~( ( ~( ( ( k2_tsep_1 @
% 0.46/0.64                                   A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 0.46/0.64                                 ( k2_tsep_1 @ A @ C @ D ) ) & 
% 0.46/0.64                               ( ( k2_tsep_1 @
% 0.46/0.64                                   A @ ( k1_tsep_1 @ A @ B @ D ) @ C ) =
% 0.46/0.64                                 ( k2_tsep_1 @ A @ D @ C ) ) ) ) & 
% 0.46/0.64                          ( ~( ( r1_tsep_1 @ C @ D ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 0.46/0.64                          ( ( r1_tsep_1 @ C @ B ) | ( r1_tsep_1 @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, axiom,
% 0.46/0.64    (![C:$i,B:$i]:
% 0.46/0.64     ( ( ( r1_tsep_1 @ B @ C ) | ( r1_tsep_1 @ C @ B ) ) =>
% 0.46/0.64       ( zip_tseitin_5 @ C @ B ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((zip_tseitin_5 @ X17 @ X18) | ~ (r1_tsep_1 @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (((zip_tseitin_5 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_4, axiom,
% 0.46/0.64    (![D:$i,C:$i]:
% 0.46/0.64     ( ( zip_tseitin_4 @ D @ C ) =>
% 0.46/0.64       ( ( r1_tsep_1 @ D @ C ) & ( r1_tsep_1 @ C @ D ) ) ))).
% 0.46/0.64  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_6, axiom,
% 0.46/0.64    (![D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_3 @ D @ C @ B @ A ) =>
% 0.46/0.64       ( ( ( k2_tsep_1 @ A @ ( k1_tsep_1 @ A @ B @ D ) @ C ) =
% 0.46/0.64           ( k2_tsep_1 @ A @ D @ C ) ) & 
% 0.46/0.64         ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 0.46/0.64           ( k2_tsep_1 @ A @ C @ D ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_8, axiom,
% 0.46/0.64    (![C:$i,B:$i]:
% 0.46/0.64     ( ( zip_tseitin_2 @ C @ B ) =>
% 0.46/0.64       ( ( r1_tsep_1 @ B @ C ) & ( r1_tsep_1 @ C @ B ) ) ))).
% 0.46/0.64  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_10, axiom,
% 0.46/0.64    (![D:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tsep_1 @ D @ C ) | ( r1_tsep_1 @ C @ D ) ) =>
% 0.46/0.64       ( zip_tseitin_1 @ D @ C ) ))).
% 0.46/0.64  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_12, axiom,
% 0.46/0.64    (![D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.46/0.64       ( ( ( k2_tsep_1 @ A @ ( k1_tsep_1 @ A @ B @ D ) @ C ) =
% 0.46/0.64           ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.46/0.64         ( ( k2_tsep_1 @ A @ C @ ( k1_tsep_1 @ A @ B @ D ) ) =
% 0.46/0.64           ( k2_tsep_1 @ A @ C @ B ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_13, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.64               ( ![D:$i]:
% 0.46/0.64                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.46/0.64                   ( ( ~( ( zip_tseitin_5 @ C @ B ) & 
% 0.46/0.64                          ( ~( zip_tseitin_4 @ D @ C ) ) & 
% 0.46/0.64                          ( ~( zip_tseitin_3 @ D @ C @ B @ A ) ) ) ) & 
% 0.46/0.64                     ( ~( ( ~( zip_tseitin_2 @ C @ B ) ) & 
% 0.46/0.64                          ( zip_tseitin_1 @ D @ C ) & 
% 0.46/0.64                          ( ~( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X19)
% 0.46/0.64          | ~ (m1_pre_topc @ X19 @ X20)
% 0.46/0.64          | (v2_struct_0 @ X21)
% 0.46/0.64          | ~ (m1_pre_topc @ X21 @ X20)
% 0.46/0.64          | (zip_tseitin_3 @ X21 @ X22 @ X19 @ X20)
% 0.46/0.64          | (zip_tseitin_4 @ X21 @ X22)
% 0.46/0.64          | ~ (zip_tseitin_5 @ X22 @ X19)
% 0.46/0.64          | ~ (m1_pre_topc @ X22 @ X20)
% 0.46/0.64          | (v2_struct_0 @ X22)
% 0.46/0.64          | ~ (l1_pre_topc @ X20)
% 0.46/0.64          | ~ (v2_pre_topc @ X20)
% 0.46/0.64          | (v2_struct_0 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (zip_tseitin_5 @ X0 @ sk_D)
% 0.46/0.64          | (zip_tseitin_4 @ X1 @ X0)
% 0.46/0.64          | (zip_tseitin_3 @ X1 @ X0 @ sk_D @ sk_A)
% 0.46/0.64          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X1)
% 0.46/0.64          | (v2_struct_0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (zip_tseitin_5 @ X0 @ sk_D)
% 0.46/0.64          | (zip_tseitin_4 @ X1 @ X0)
% 0.46/0.64          | (zip_tseitin_3 @ X1 @ X0 @ sk_D @ sk_A)
% 0.46/0.64          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X1)
% 0.46/0.64          | (v2_struct_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_D)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | (zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A)
% 0.46/0.64          | (zip_tseitin_4 @ X0 @ sk_C)
% 0.46/0.64          | ~ (zip_tseitin_5 @ sk_C @ sk_D)
% 0.46/0.64          | (v2_struct_0 @ sk_C)
% 0.46/0.64          | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          ((v2_struct_0 @ sk_A)
% 0.46/0.64           | (v2_struct_0 @ sk_C)
% 0.46/0.64           | (zip_tseitin_4 @ X0 @ sk_C)
% 0.46/0.64           | (zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A)
% 0.46/0.64           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64           | (v2_struct_0 @ X0)
% 0.46/0.64           | (v2_struct_0 @ sk_D)))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (zip_tseitin_3 @ sk_B @ sk_C @ sk_D @ sk_A)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['12'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((zip_tseitin_5 @ X17 @ X18) | ~ (r1_tsep_1 @ X18 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (((zip_tseitin_5 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_D)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | (zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A)
% 0.46/0.64          | (zip_tseitin_4 @ X0 @ sk_C)
% 0.46/0.64          | ~ (zip_tseitin_5 @ sk_C @ sk_D)
% 0.46/0.64          | (v2_struct_0 @ sk_C)
% 0.46/0.64          | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '22'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((![X0 : $i]:
% 0.46/0.64          ((v2_struct_0 @ sk_A)
% 0.46/0.64           | (v2_struct_0 @ sk_C)
% 0.46/0.64           | (zip_tseitin_4 @ X0 @ sk_C)
% 0.46/0.64           | (zip_tseitin_3 @ X0 @ sk_C @ sk_D @ sk_A)
% 0.46/0.64           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64           | (v2_struct_0 @ X0)
% 0.46/0.64           | (v2_struct_0 @ sk_D)))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (zip_tseitin_3 @ sk_B @ sk_C @ sk_D @ sk_A)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.64         (((k2_tsep_1 @ X11 @ X13 @ (k1_tsep_1 @ X11 @ X14 @ X12))
% 0.46/0.64            = (k2_tsep_1 @ X11 @ X13 @ X12))
% 0.46/0.64          | ~ (zip_tseitin_3 @ X12 @ X13 @ X14 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | ((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64             = (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64          != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64            != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64          != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('split', [status(esa)], ['12'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ X7 @ X8) | ~ (r1_tsep_1 @ X8 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X19)
% 0.46/0.64          | ~ (m1_pre_topc @ X19 @ X20)
% 0.46/0.64          | (v2_struct_0 @ X21)
% 0.46/0.64          | ~ (m1_pre_topc @ X21 @ X20)
% 0.46/0.64          | (zip_tseitin_0 @ X21 @ X22 @ X19 @ X20)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X21 @ X22)
% 0.46/0.64          | (zip_tseitin_2 @ X22 @ X19)
% 0.46/0.64          | ~ (m1_pre_topc @ X22 @ X20)
% 0.46/0.64          | (v2_struct_0 @ X22)
% 0.46/0.64          | ~ (l1_pre_topc @ X20)
% 0.46/0.64          | ~ (v2_pre_topc @ X20)
% 0.46/0.64          | (v2_struct_0 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | (zip_tseitin_2 @ X0 @ sk_B)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X1 @ X0)
% 0.46/0.64          | (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 0.46/0.64          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X1)
% 0.46/0.64          | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | (zip_tseitin_2 @ X0 @ sk_B)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X1 @ X0)
% 0.46/0.64          | (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 0.46/0.64          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X1)
% 0.46/0.64          | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_B)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X0 @ sk_C)
% 0.46/0.64          | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64          | (v2_struct_0 @ sk_C)
% 0.46/0.64          | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64        | ~ (zip_tseitin_1 @ sk_D @ sk_C)
% 0.46/0.64        | (zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_D)
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '51'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         (((k2_tsep_1 @ X3 @ X5 @ (k1_tsep_1 @ X3 @ X4 @ X6))
% 0.46/0.64            = (k2_tsep_1 @ X3 @ X5 @ X4))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X6 @ X5 @ X4 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | ((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64             = (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64          != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (((((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64           != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (((((k2_tsep_1 @ sk_A @ sk_C @ sk_B) != (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.64  thf('59', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('60', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t22_tmap_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.64               ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.64                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ X1)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ X2)
% 0.46/0.64          | ~ (r1_tsep_1 @ X2 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X2 @ X1)
% 0.46/0.64          | (v2_struct_0 @ X2)
% 0.46/0.64          | ~ (l1_pre_topc @ X1)
% 0.46/0.64          | ~ (v2_pre_topc @ X1)
% 0.46/0.64          | (v2_struct_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t22_tmap_1])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.46/0.64          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.46/0.64          | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.46/0.64          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.46/0.64          | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '65'])).
% 0.46/0.64  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['58', '68'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         ((r1_tsep_1 @ X9 @ X10) | ~ (zip_tseitin_2 @ X10 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ X1)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ X2)
% 0.46/0.64          | ~ (r1_tsep_1 @ X0 @ X2)
% 0.46/0.64          | ~ (m1_pre_topc @ X2 @ X1)
% 0.46/0.64          | (v2_struct_0 @ X2)
% 0.46/0.64          | ~ (l1_pre_topc @ X1)
% 0.46/0.64          | ~ (v2_pre_topc @ X1)
% 0.46/0.64          | (v2_struct_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t22_tmap_1])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.46/0.64          | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.64  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.46/0.64          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.46/0.64          | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['73', '79'])).
% 0.46/0.64  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '82'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['83'])).
% 0.46/0.64  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['84', '85'])).
% 0.46/0.64  thf('87', plain, (~ (v2_struct_0 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('clc', [status(thm)], ['86', '87'])).
% 0.46/0.64  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('clc', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.46/0.64       ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['12'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ X7 @ X8) | ~ (r1_tsep_1 @ X7 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64        | ~ (zip_tseitin_1 @ sk_D @ sk_C)
% 0.46/0.64        | (zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_D)
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '50'])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_0 @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         (((k2_tsep_1 @ X3 @ X5 @ (k1_tsep_1 @ X3 @ X4 @ X6))
% 0.46/0.64            = (k2_tsep_1 @ X3 @ X5 @ X4))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X6 @ X5 @ X4 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | ((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64             = (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64          != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (((((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64           != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (((((k2_tsep_1 @ sk_A @ sk_C @ sk_B) != (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['93', '102'])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['103'])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_2 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['106'])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         ((r1_tsep_1 @ X9 @ X10) | ~ (zip_tseitin_2 @ X10 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['111'])).
% 0.46/0.64  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.64  thf('115', plain, (~ (v2_struct_0 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('clc', [status(thm)], ['114', '115'])).
% 0.46/0.64  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_C))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64                = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) & 
% 0.46/0.64             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('clc', [status(thm)], ['116', '117'])).
% 0.46/0.64  thf('119', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.46/0.64       ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.64  thf('121', plain,
% 0.46/0.64      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.46/0.64      inference('split', [status(esa)], ['12'])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (~
% 0.46/0.64       (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.46/0.64       ~
% 0.46/0.64       (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.64          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.46/0.64      inference('split', [status(esa)], ['36'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (~
% 0.46/0.64       (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['92', '120', '121', '122'])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64         != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['37', '123'])).
% 0.46/0.64  thf('125', plain,
% 0.46/0.64      (((((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64           != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '124'])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (((((k2_tsep_1 @ sk_A @ sk_C @ sk_B) != (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '125'])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('129', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.64  thf('130', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['129'])).
% 0.46/0.64  thf('131', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((r1_tsep_1 @ X15 @ X16) | ~ (zip_tseitin_4 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.64  thf('132', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D)
% 0.46/0.64         | (r1_tsep_1 @ sk_B @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.64  thf('133', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('134', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['132', '133'])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_A)
% 0.46/0.64         | (v2_struct_0 @ sk_B)
% 0.46/0.64         | (v2_struct_0 @ sk_C)
% 0.46/0.64         | (v2_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['134'])).
% 0.46/0.64  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['135', '136'])).
% 0.46/0.64  thf('138', plain, (~ (v2_struct_0 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('139', plain,
% 0.46/0.64      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.46/0.64         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('clc', [status(thm)], ['137', '138'])).
% 0.46/0.64  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('141', plain, (((v2_struct_0 @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.46/0.64      inference('clc', [status(thm)], ['139', '140'])).
% 0.46/0.64  thf('142', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('143', plain, (~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['141', '142'])).
% 0.46/0.64  thf('144', plain, (((r1_tsep_1 @ sk_C @ sk_D))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['143', '121'])).
% 0.46/0.64  thf('145', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_D)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (zip_tseitin_3 @ sk_B @ sk_C @ sk_D @ sk_A)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['25', '144'])).
% 0.46/0.64  thf('146', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.64         (((k2_tsep_1 @ X11 @ X13 @ (k1_tsep_1 @ X11 @ X14 @ X12))
% 0.46/0.64            = (k2_tsep_1 @ X11 @ X13 @ X12))
% 0.46/0.64          | ~ (zip_tseitin_3 @ X12 @ X13 @ X14 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.46/0.64  thf('147', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_D)
% 0.46/0.64        | ((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64            = (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['145', '146'])).
% 0.46/0.64  thf('148', plain,
% 0.46/0.64      (((k2_tsep_1 @ sk_A @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_B))
% 0.46/0.64         != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['37', '123'])).
% 0.46/0.64  thf('149', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ sk_B)
% 0.46/0.64          != (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.64        | (v2_struct_0 @ sk_D)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['147', '148'])).
% 0.46/0.64  thf('150', plain,
% 0.46/0.64      ((((k2_tsep_1 @ sk_A @ sk_C @ sk_B) != (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '149'])).
% 0.46/0.64  thf('151', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_D)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['150'])).
% 0.46/0.64  thf('152', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_C @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('153', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_D)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['151', '152'])).
% 0.46/0.64  thf('154', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_D)
% 0.46/0.64        | (zip_tseitin_4 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['153'])).
% 0.46/0.64  thf('155', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((r1_tsep_1 @ X15 @ X16) | ~ (zip_tseitin_4 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.64  thf('156', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_D)
% 0.46/0.64        | (r1_tsep_1 @ sk_B @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['154', '155'])).
% 0.46/0.64  thf('157', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('158', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_D)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['156', '157'])).
% 0.46/0.64  thf('159', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_D))),
% 0.46/0.64      inference('simplify', [status(thm)], ['158'])).
% 0.46/0.64  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('161', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['159', '160'])).
% 0.46/0.64  thf('162', plain, (~ (v2_struct_0 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('163', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.46/0.64      inference('clc', [status(thm)], ['161', '162'])).
% 0.46/0.64  thf('164', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('165', plain, ((v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('clc', [status(thm)], ['163', '164'])).
% 0.46/0.64  thf('166', plain, ($false), inference('demod', [status(thm)], ['0', '165'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
