%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NGMGg8EhEo

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:32 EST 2020

% Result     : Theorem 25.42s
% Output     : Refutation 25.42s
% Verified   : 
% Statistics : Number of formulae       :  379 (1582 expanded)
%              Number of leaves         :   24 ( 427 expanded)
%              Depth                    :   53
%              Number of atoms          : 6428 (49930 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t34_tmap_1,conjecture,(
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
                 => ( ~ ( r1_tsep_1 @ B @ C )
                   => ( ( ( m1_pre_topc @ B @ D )
                       => ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ C ) @ B )
                          & ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ C @ D ) @ B ) ) )
                      & ( ( m1_pre_topc @ C @ D )
                       => ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ D ) @ C )
                          & ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ B ) @ C ) ) ) ) ) ) ) ) ) )).

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
                   => ( ~ ( r1_tsep_1 @ B @ C )
                     => ( ( ( m1_pre_topc @ B @ D )
                         => ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ C ) @ B )
                            & ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ C @ D ) @ B ) ) )
                        & ( ( m1_pre_topc @ C @ D )
                         => ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ D ) @ C )
                            & ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ B ) @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tsep_1,axiom,(
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
               => ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tsep_1 @ X19 @ X21 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t24_tmap_1,axiom,(
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
                   => ( ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ B @ D ) )
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
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ B )
     => ( ( r1_tsep_1 @ B @ D )
        & ( r1_tsep_1 @ D @ B ) ) ) )).

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
                      | ( zip_tseitin_0 @ D @ B ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( zip_tseitin_0 @ X17 @ X15 )
      | ( zip_tseitin_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X11 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_tmap_1,axiom,(
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
                 => ( ~ ( r1_tsep_1 @ B @ C )
                   => ( ( ( m1_pre_topc @ B @ D )
                       => ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ D @ C ) ) )
                      & ( ( m1_pre_topc @ C @ D )
                       => ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X23 @ X22 @ X25 ) @ ( k2_tsep_1 @ X23 @ X24 @ X25 ) )
      | ( r1_tsep_1 @ X22 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t32_tmap_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ X0 @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

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

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X10 )
      | ~ ( r1_tsep_1 @ X8 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['36','58'])).

thf('60',plain,
    ( ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['6','60'])).

thf('62',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X14 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('69',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('76',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('100',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tsep_1 @ X19 @ X21 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X11 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['94'])).

thf('118',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X23 @ X22 @ X25 ) @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) )
      | ( r1_tsep_1 @ X22 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t32_tmap_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['116','131'])).

thf('133',plain,
    ( ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['98','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(split,[status(esa)],['63'])).

thf('137',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X14 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('138',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( zip_tseitin_0 @ sk_B @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_0 @ sk_B @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X11 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('179',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('191',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tsep_1 @ X19 @ X21 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['191','197'])).

thf('199',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['199','204'])).

thf('206',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( zip_tseitin_0 @ X17 @ X15 )
      | ( zip_tseitin_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['198','211'])).

thf('213',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( zip_tseitin_1 @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','215'])).

thf('217',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X11 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['94'])).

thf('221',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X23 @ X22 @ X25 ) @ ( k2_tsep_1 @ X23 @ X24 @ X25 ) )
      | ( r1_tsep_1 @ X22 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t32_tmap_1])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ ( k2_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ ( k2_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ X0 @ sk_B ) )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['222','228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['221','229'])).

thf('231',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['220','230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['199','204'])).

thf('233',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X10 )
      | ~ ( r1_tsep_1 @ X8 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['231','238'])).

thf('240',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('242',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('246',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tsep_1 @ X19 @ X21 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['246','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['245','258'])).

thf('260',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
    | ( zip_tseitin_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X11 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['37'])).

thf('264',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X23 @ X22 @ X25 ) @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) )
      | ( r1_tsep_1 @ X22 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t32_tmap_1])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ ( k2_tsep_1 @ sk_A @ sk_C @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ ( k2_tsep_1 @ sk_A @ sk_C @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['265','271'])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['264','272'])).

thf('274',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['263','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('276',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_A )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_A )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['262','277'])).

thf('279',plain,
    ( ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['244','279'])).

thf('281',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('283',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X14 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('284',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['281','284'])).

thf('286',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('287',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['287','288','289','290'])).

thf('292',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('294',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['294','295','296','297'])).

thf('299',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('301',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( zip_tseitin_1 @ sk_B @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['241','301'])).

thf('303',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( m1_pre_topc @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('313',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['94'])).

thf('314',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['311','312','93','313'])).

thf('315',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['240','314'])).

thf('316',plain,
    ( ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','315'])).

thf('317',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['189','317'])).

thf('319',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['63'])).

thf('321',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X14 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('322',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['319','322'])).

thf('324',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('325',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('330',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['329'])).

thf('331',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('332',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['330','331'])).

thf('333',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['332','333','334','335'])).

thf('337',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_B ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('339',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( zip_tseitin_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['186','339'])).

thf('341',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['340'])).

thf('342',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(clc,[status(thm)],['343','344'])).

thf('346',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('348',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(split,[status(esa)],['37'])).

thf('351',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('352',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) @ sk_B )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['63'])).

thf('353',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['91','93','95','163','349','350','351','352'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NGMGg8EhEo
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:39:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 25.42/25.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.42/25.67  % Solved by: fo/fo7.sh
% 25.42/25.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.42/25.67  % done 8008 iterations in 25.194s
% 25.42/25.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.42/25.67  % SZS output start Refutation
% 25.42/25.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 25.42/25.67  thf(sk_D_type, type, sk_D: $i).
% 25.42/25.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 25.42/25.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 25.42/25.67  thf(sk_A_type, type, sk_A: $i).
% 25.42/25.67  thf(sk_C_type, type, sk_C: $i).
% 25.42/25.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 25.42/25.67  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 25.42/25.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 25.42/25.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 25.42/25.67  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 25.42/25.67  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 25.42/25.67  thf(sk_B_type, type, sk_B: $i).
% 25.42/25.67  thf(t34_tmap_1, conjecture,
% 25.42/25.67    (![A:$i]:
% 25.42/25.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 25.42/25.67       ( ![B:$i]:
% 25.42/25.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 25.42/25.67           ( ![C:$i]:
% 25.42/25.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67               ( ![D:$i]:
% 25.42/25.67                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 25.42/25.67                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 25.42/25.67                     ( ( ( m1_pre_topc @ B @ D ) =>
% 25.42/25.67                         ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ C ) @ B ) ) & 
% 25.42/25.67                           ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ C @ D ) @ B ) ) ) ) & 
% 25.42/25.67                       ( ( m1_pre_topc @ C @ D ) =>
% 25.42/25.67                         ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ D ) @ C ) ) & 
% 25.42/25.67                           ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ B ) @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 25.42/25.67  thf(zf_stmt_0, negated_conjecture,
% 25.42/25.67    (~( ![A:$i]:
% 25.42/25.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 25.42/25.67            ( l1_pre_topc @ A ) ) =>
% 25.42/25.67          ( ![B:$i]:
% 25.42/25.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 25.42/25.67              ( ![C:$i]:
% 25.42/25.67                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67                  ( ![D:$i]:
% 25.42/25.67                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 25.42/25.67                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 25.42/25.67                        ( ( ( m1_pre_topc @ B @ D ) =>
% 25.42/25.67                            ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ C ) @ B ) ) & 
% 25.42/25.67                              ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ C @ D ) @ B ) ) ) ) & 
% 25.42/25.67                          ( ( m1_pre_topc @ C @ D ) =>
% 25.42/25.67                            ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ D ) @ C ) ) & 
% 25.42/25.67                              ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ D @ B ) @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 25.42/25.67    inference('cnf.neg', [status(esa)], [t34_tmap_1])).
% 25.42/25.67  thf('0', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf(dt_k2_tsep_1, axiom,
% 25.42/25.67    (![A:$i,B:$i,C:$i]:
% 25.42/25.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 25.42/25.67         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 25.42/25.67         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 25.42/25.67         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 25.42/25.67         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 25.42/25.67  thf('2', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X4 @ X3 @ X5) @ X4))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('3', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_D))),
% 25.42/25.67      inference('sup-', [status(thm)], ['1', '2'])).
% 25.42/25.67  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('5', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_D))),
% 25.42/25.67      inference('demod', [status(thm)], ['3', '4'])).
% 25.42/25.67  thf('6', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['0', '5'])).
% 25.42/25.67  thf('7', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['0', '5'])).
% 25.42/25.67  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf(t30_tsep_1, axiom,
% 25.42/25.67    (![A:$i]:
% 25.42/25.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 25.42/25.67       ( ![B:$i]:
% 25.42/25.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 25.42/25.67           ( ![C:$i]:
% 25.42/25.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 25.42/25.67                 ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B ) & 
% 25.42/25.67                   ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) ) ))).
% 25.42/25.67  thf('10', plain,
% 25.42/25.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X19)
% 25.42/25.67          | ~ (m1_pre_topc @ X19 @ X20)
% 25.42/25.67          | (r1_tsep_1 @ X19 @ X21)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X20 @ X19 @ X21) @ X19)
% 25.42/25.67          | ~ (m1_pre_topc @ X21 @ X20)
% 25.42/25.67          | (v2_struct_0 @ X21)
% 25.42/25.67          | ~ (l1_pre_topc @ X20)
% 25.42/25.67          | ~ (v2_pre_topc @ X20)
% 25.42/25.67          | (v2_struct_0 @ X20))),
% 25.42/25.67      inference('cnf', [status(esa)], [t30_tsep_1])).
% 25.42/25.67  thf('11', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['9', '10'])).
% 25.42/25.67  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('14', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['11', '12', '13'])).
% 25.42/25.67  thf('15', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['8', '14'])).
% 25.42/25.67  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('18', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X4 @ X3 @ X5) @ X4))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('19', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['17', '18'])).
% 25.42/25.67  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('21', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['19', '20'])).
% 25.42/25.67  thf('22', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['16', '21'])).
% 25.42/25.67  thf(t24_tmap_1, axiom,
% 25.42/25.67    (![A:$i]:
% 25.42/25.67     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 25.42/25.67       ( ![B:$i]:
% 25.42/25.67         ( ( ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 25.42/25.67           ( ![C:$i]:
% 25.42/25.67             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 25.42/25.67               ( ![D:$i]:
% 25.42/25.67                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 25.42/25.67                   ( ( m1_pre_topc @ B @ C ) =>
% 25.42/25.67                     ( ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ B @ D ) ) | 
% 25.42/25.67                       ( ( ~( r1_tsep_1 @ D @ C ) ) & 
% 25.42/25.67                         ( ~( r1_tsep_1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 25.42/25.67  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 25.42/25.67  thf(zf_stmt_2, axiom,
% 25.42/25.67    (![D:$i,C:$i]:
% 25.42/25.67     ( ( zip_tseitin_1 @ D @ C ) =>
% 25.42/25.67       ( ( ~( r1_tsep_1 @ C @ D ) ) & ( ~( r1_tsep_1 @ D @ C ) ) ) ))).
% 25.42/25.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 25.42/25.67  thf(zf_stmt_4, axiom,
% 25.42/25.67    (![D:$i,B:$i]:
% 25.42/25.67     ( ( zip_tseitin_0 @ D @ B ) =>
% 25.42/25.67       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ))).
% 25.42/25.67  thf(zf_stmt_5, axiom,
% 25.42/25.67    (![A:$i]:
% 25.42/25.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 25.42/25.67       ( ![B:$i]:
% 25.42/25.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 25.42/25.67           ( ![C:$i]:
% 25.42/25.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67               ( ![D:$i]:
% 25.42/25.67                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 25.42/25.67                   ( ( m1_pre_topc @ B @ C ) =>
% 25.42/25.67                     ( ( zip_tseitin_1 @ D @ C ) | ( zip_tseitin_0 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 25.42/25.67  thf('23', plain,
% 25.42/25.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X15)
% 25.42/25.67          | ~ (m1_pre_topc @ X15 @ X16)
% 25.42/25.67          | (v2_struct_0 @ X17)
% 25.42/25.67          | ~ (m1_pre_topc @ X17 @ X16)
% 25.42/25.67          | (zip_tseitin_0 @ X17 @ X15)
% 25.42/25.67          | (zip_tseitin_1 @ X17 @ X18)
% 25.42/25.67          | ~ (m1_pre_topc @ X15 @ X18)
% 25.42/25.67          | ~ (m1_pre_topc @ X18 @ X16)
% 25.42/25.67          | (v2_struct_0 @ X18)
% 25.42/25.67          | ~ (l1_pre_topc @ X16)
% 25.42/25.67          | ~ (v2_pre_topc @ X16)
% 25.42/25.67          | (v2_struct_0 @ X16))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.42/25.67  thf('24', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['22', '23'])).
% 25.42/25.67  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('27', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('demod', [status(thm)], ['24', '25', '26'])).
% 25.42/25.67  thf('28', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['27'])).
% 25.42/25.67  thf('29', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_B)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['15', '28'])).
% 25.42/25.67  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('31', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_B)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('demod', [status(thm)], ['29', '30'])).
% 25.42/25.67  thf('32', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('simplify', [status(thm)], ['31'])).
% 25.42/25.67  thf('33', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['7', '32'])).
% 25.42/25.67  thf('34', plain,
% 25.42/25.67      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['33'])).
% 25.42/25.67  thf('35', plain,
% 25.42/25.67      (![X11 : $i, X12 : $i]:
% 25.42/25.67         ((r1_tsep_1 @ X11 @ X12) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.42/25.67  thf('36', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['34', '35'])).
% 25.42/25.67  thf('37', plain,
% 25.42/25.67      (((m1_pre_topc @ sk_B @ sk_D)
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('38', plain,
% 25.42/25.67      (((m1_pre_topc @ sk_B @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('split', [status(esa)], ['37'])).
% 25.42/25.67  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('41', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf(t32_tmap_1, axiom,
% 25.42/25.67    (![A:$i]:
% 25.42/25.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 25.42/25.67       ( ![B:$i]:
% 25.42/25.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 25.42/25.67           ( ![C:$i]:
% 25.42/25.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67               ( ![D:$i]:
% 25.42/25.67                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 25.42/25.67                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 25.42/25.67                     ( ( ( m1_pre_topc @ B @ D ) =>
% 25.42/25.67                         ( m1_pre_topc @
% 25.42/25.67                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 25.42/25.67                           ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 25.42/25.67                       ( ( m1_pre_topc @ C @ D ) =>
% 25.42/25.67                         ( m1_pre_topc @
% 25.42/25.67                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 25.42/25.67                           ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 25.42/25.67  thf('42', plain,
% 25.42/25.67      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X22)
% 25.42/25.67          | ~ (m1_pre_topc @ X22 @ X23)
% 25.42/25.67          | (v2_struct_0 @ X24)
% 25.42/25.67          | ~ (m1_pre_topc @ X24 @ X23)
% 25.42/25.67          | ~ (m1_pre_topc @ X22 @ X24)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X23 @ X22 @ X25) @ 
% 25.42/25.67             (k2_tsep_1 @ X23 @ X24 @ X25))
% 25.42/25.67          | (r1_tsep_1 @ X22 @ X25)
% 25.42/25.67          | ~ (m1_pre_topc @ X25 @ X23)
% 25.42/25.67          | (v2_struct_0 @ X25)
% 25.42/25.67          | ~ (l1_pre_topc @ X23)
% 25.42/25.67          | ~ (v2_pre_topc @ X23)
% 25.42/25.67          | (v2_struct_0 @ X23))),
% 25.42/25.67      inference('cnf', [status(esa)], [t32_tmap_1])).
% 25.42/25.67  thf('43', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 25.42/25.67             (k2_tsep_1 @ sk_A @ X1 @ X0))
% 25.42/25.67          | ~ (m1_pre_topc @ sk_B @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['41', '42'])).
% 25.42/25.67  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('46', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 25.42/25.67             (k2_tsep_1 @ sk_A @ X1 @ X0))
% 25.42/25.67          | ~ (m1_pre_topc @ sk_B @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['43', '44', '45'])).
% 25.42/25.67  thf('47', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ sk_B @ X0)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67             (k2_tsep_1 @ sk_A @ X0 @ sk_C))
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['40', '46'])).
% 25.42/25.67  thf('48', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67        | ~ (m1_pre_topc @ sk_B @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['39', '47'])).
% 25.42/25.67  thf('49', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['38', '48'])).
% 25.42/25.67  thf('50', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['16', '21'])).
% 25.42/25.67  thf(t22_tmap_1, axiom,
% 25.42/25.67    (![A:$i]:
% 25.42/25.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 25.42/25.67       ( ![B:$i]:
% 25.42/25.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 25.42/25.67           ( ![C:$i]:
% 25.42/25.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 25.42/25.67               ( ( m1_pre_topc @ B @ C ) =>
% 25.42/25.67                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 25.42/25.67  thf('51', plain,
% 25.42/25.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X8)
% 25.42/25.67          | ~ (m1_pre_topc @ X8 @ X9)
% 25.42/25.67          | ~ (m1_pre_topc @ X8 @ X10)
% 25.42/25.67          | ~ (r1_tsep_1 @ X8 @ X10)
% 25.42/25.67          | ~ (m1_pre_topc @ X10 @ X9)
% 25.42/25.67          | (v2_struct_0 @ X10)
% 25.42/25.67          | ~ (l1_pre_topc @ X9)
% 25.42/25.67          | ~ (v2_pre_topc @ X9)
% 25.42/25.67          | (v2_struct_0 @ X9))),
% 25.42/25.67      inference('cnf', [status(esa)], [t22_tmap_1])).
% 25.42/25.67  thf('52', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['50', '51'])).
% 25.42/25.67  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('55', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('demod', [status(thm)], ['52', '53', '54'])).
% 25.42/25.67  thf('56', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['55'])).
% 25.42/25.67  thf('57', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_A)
% 25.42/25.67         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67              (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 25.42/25.67         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['49', '56'])).
% 25.42/25.67  thf('58', plain,
% 25.42/25.67      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67              (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['57'])).
% 25.42/25.67  thf('59', plain,
% 25.42/25.67      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 25.42/25.67         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['36', '58'])).
% 25.42/25.67  thf('60', plain,
% 25.42/25.67      (((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 25.42/25.67         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['59'])).
% 25.42/25.67  thf('61', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['6', '60'])).
% 25.42/25.67  thf('62', plain,
% 25.42/25.67      ((((r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['61'])).
% 25.42/25.67  thf('63', plain,
% 25.42/25.67      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('64', plain,
% 25.42/25.67      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)))),
% 25.42/25.67      inference('split', [status(esa)], ['63'])).
% 25.42/25.67  thf('65', plain,
% 25.42/25.67      (![X13 : $i, X14 : $i]:
% 25.42/25.67         (~ (r1_tsep_1 @ X14 @ X13) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.42/25.67  thf('66', plain,
% 25.42/25.67      ((~ (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['64', '65'])).
% 25.42/25.67  thf('67', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['62', '66'])).
% 25.42/25.67  thf('68', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('69', plain,
% 25.42/25.67      ((((r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_D @ sk_A)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['67', '68'])).
% 25.42/25.67  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('72', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('73', plain,
% 25.42/25.67      ((((r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 25.42/25.67  thf('74', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['73'])).
% 25.42/25.67  thf('75', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('76', plain,
% 25.42/25.67      ((((r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['74', '75'])).
% 25.42/25.67  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('79', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('80', plain,
% 25.42/25.67      ((((r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 25.42/25.67  thf('81', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['80'])).
% 25.42/25.67  thf('82', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('83', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['81', '82'])).
% 25.42/25.67  thf('84', plain, (~ (v2_struct_0 @ sk_D)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('85', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['83', '84'])).
% 25.42/25.67  thf('86', plain, (~ (v2_struct_0 @ sk_C)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('87', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('clc', [status(thm)], ['85', '86'])).
% 25.42/25.67  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('89', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.67      inference('clc', [status(thm)], ['87', '88'])).
% 25.42/25.67  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('91', plain,
% 25.42/25.67      (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) | 
% 25.42/25.67       ~ ((m1_pre_topc @ sk_B @ sk_D))),
% 25.42/25.67      inference('sup-', [status(thm)], ['89', '90'])).
% 25.42/25.67  thf('92', plain,
% 25.42/25.67      (((m1_pre_topc @ sk_B @ sk_D) | (m1_pre_topc @ sk_C @ sk_D))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('93', plain,
% 25.42/25.67      (((m1_pre_topc @ sk_C @ sk_D)) | ((m1_pre_topc @ sk_B @ sk_D))),
% 25.42/25.67      inference('split', [status(esa)], ['92'])).
% 25.42/25.67  thf('94', plain,
% 25.42/25.67      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)
% 25.42/25.67        | (m1_pre_topc @ sk_C @ sk_D))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('95', plain,
% 25.42/25.67      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 25.42/25.67       ((m1_pre_topc @ sk_C @ sk_D)) | 
% 25.42/25.67       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B))),
% 25.42/25.67      inference('split', [status(esa)], ['94'])).
% 25.42/25.67  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('97', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['19', '20'])).
% 25.42/25.67  thf('98', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['96', '97'])).
% 25.42/25.67  thf('99', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['96', '97'])).
% 25.42/25.67  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('101', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('102', plain,
% 25.42/25.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X19)
% 25.42/25.67          | ~ (m1_pre_topc @ X19 @ X20)
% 25.42/25.67          | (r1_tsep_1 @ X19 @ X21)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X20 @ X19 @ X21) @ X21)
% 25.42/25.67          | ~ (m1_pre_topc @ X21 @ X20)
% 25.42/25.67          | (v2_struct_0 @ X21)
% 25.42/25.67          | ~ (l1_pre_topc @ X20)
% 25.42/25.67          | ~ (v2_pre_topc @ X20)
% 25.42/25.67          | (v2_struct_0 @ X20))),
% 25.42/25.67      inference('cnf', [status(esa)], [t30_tsep_1])).
% 25.42/25.67  thf('103', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X0)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['101', '102'])).
% 25.42/25.67  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('106', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X0)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['103', '104', '105'])).
% 25.42/25.67  thf('107', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['100', '106'])).
% 25.42/25.67  thf('108', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['27'])).
% 25.42/25.67  thf('109', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['107', '108'])).
% 25.42/25.67  thf('110', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('111', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('demod', [status(thm)], ['109', '110'])).
% 25.42/25.67  thf('112', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('simplify', [status(thm)], ['111'])).
% 25.42/25.67  thf('113', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['99', '112'])).
% 25.42/25.67  thf('114', plain,
% 25.42/25.67      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_D))),
% 25.42/25.67      inference('simplify', [status(thm)], ['113'])).
% 25.42/25.67  thf('115', plain,
% 25.42/25.67      (![X11 : $i, X12 : $i]:
% 25.42/25.67         ((r1_tsep_1 @ X11 @ X12) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.42/25.67  thf('116', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['114', '115'])).
% 25.42/25.67  thf('117', plain,
% 25.42/25.67      (((m1_pre_topc @ sk_C @ sk_D)) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('split', [status(esa)], ['94'])).
% 25.42/25.67  thf('118', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('119', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('120', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('121', plain,
% 25.42/25.67      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X22)
% 25.42/25.67          | ~ (m1_pre_topc @ X22 @ X23)
% 25.42/25.67          | (v2_struct_0 @ X24)
% 25.42/25.67          | ~ (m1_pre_topc @ X24 @ X23)
% 25.42/25.67          | ~ (m1_pre_topc @ X25 @ X24)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X23 @ X22 @ X25) @ 
% 25.42/25.67             (k2_tsep_1 @ X23 @ X22 @ X24))
% 25.42/25.67          | (r1_tsep_1 @ X22 @ X25)
% 25.42/25.67          | ~ (m1_pre_topc @ X25 @ X23)
% 25.42/25.67          | (v2_struct_0 @ X25)
% 25.42/25.67          | ~ (l1_pre_topc @ X23)
% 25.42/25.67          | ~ (v2_pre_topc @ X23)
% 25.42/25.67          | (v2_struct_0 @ X23))),
% 25.42/25.67      inference('cnf', [status(esa)], [t32_tmap_1])).
% 25.42/25.67  thf('122', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 25.42/25.67             (k2_tsep_1 @ sk_A @ sk_B @ X1))
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['120', '121'])).
% 25.42/25.67  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('125', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ X0)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 25.42/25.67             (k2_tsep_1 @ sk_A @ sk_B @ X1))
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['122', '123', '124'])).
% 25.42/25.67  thf('126', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ sk_C @ X0)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['119', '125'])).
% 25.42/25.67  thf('127', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67           (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['118', '126'])).
% 25.42/25.67  thf('128', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67            (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['117', '127'])).
% 25.42/25.67  thf('129', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['55'])).
% 25.42/25.67  thf('130', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A)
% 25.42/25.67         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67              (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 25.42/25.67         <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['128', '129'])).
% 25.42/25.67  thf('131', plain,
% 25.42/25.67      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 25.42/25.67              (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['130'])).
% 25.42/25.67  thf('132', plain,
% 25.42/25.67      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 25.42/25.67         <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['116', '131'])).
% 25.42/25.67  thf('133', plain,
% 25.42/25.67      (((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 25.42/25.67         <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['132'])).
% 25.42/25.67  thf('134', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['98', '133'])).
% 25.42/25.67  thf('135', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['134'])).
% 25.42/25.67  thf('136', plain,
% 25.42/25.67      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)))),
% 25.42/25.67      inference('split', [status(esa)], ['63'])).
% 25.42/25.67  thf('137', plain,
% 25.42/25.67      (![X13 : $i, X14 : $i]:
% 25.42/25.67         (~ (r1_tsep_1 @ X14 @ X13) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.42/25.67  thf('138', plain,
% 25.42/25.67      ((~ (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['136', '137'])).
% 25.42/25.67  thf('139', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['135', '138'])).
% 25.42/25.67  thf('140', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('141', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['139', '140'])).
% 25.42/25.67  thf('142', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('144', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('145', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 25.42/25.67  thf('146', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['145'])).
% 25.42/25.67  thf('147', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('148', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['146', '147'])).
% 25.42/25.67  thf('149', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('151', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('152', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 25.42/25.67  thf('153', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_D)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['152'])).
% 25.42/25.67  thf('154', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('155', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C)
% 25.42/25.67         | (v2_struct_0 @ sk_B)
% 25.42/25.67         | (v2_struct_0 @ sk_A)
% 25.42/25.67         | (v2_struct_0 @ sk_D)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['153', '154'])).
% 25.42/25.67  thf('156', plain, (~ (v2_struct_0 @ sk_D)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('157', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['155', '156'])).
% 25.42/25.67  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('159', plain,
% 25.42/25.67      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('clc', [status(thm)], ['157', '158'])).
% 25.42/25.67  thf('160', plain, (~ (v2_struct_0 @ sk_C)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('161', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B))
% 25.42/25.67         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) & 
% 25.42/25.67             ((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.67      inference('clc', [status(thm)], ['159', '160'])).
% 25.42/25.67  thf('162', plain, (~ (v2_struct_0 @ sk_B)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('163', plain,
% 25.42/25.67      (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) | 
% 25.42/25.67       ~ ((m1_pre_topc @ sk_C @ sk_D))),
% 25.42/25.67      inference('sup-', [status(thm)], ['161', '162'])).
% 25.42/25.67  thf('164', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('165', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('simplify', [status(thm)], ['111'])).
% 25.42/25.67  thf('166', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (zip_tseitin_0 @ sk_B @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['164', '165'])).
% 25.42/25.67  thf('167', plain,
% 25.42/25.67      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (zip_tseitin_0 @ sk_B @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('simplify', [status(thm)], ['166'])).
% 25.42/25.67  thf('168', plain,
% 25.42/25.67      (![X11 : $i, X12 : $i]:
% 25.42/25.67         ((r1_tsep_1 @ X11 @ X12) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.42/25.67  thf('169', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 25.42/25.67      inference('sup-', [status(thm)], ['167', '168'])).
% 25.42/25.67  thf('170', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['8', '14'])).
% 25.42/25.67  thf('171', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['55'])).
% 25.42/25.67  thf('172', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 25.42/25.67        | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['170', '171'])).
% 25.42/25.67  thf('173', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('174', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('demod', [status(thm)], ['172', '173'])).
% 25.42/25.67  thf('175', plain,
% 25.42/25.67      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('simplify', [status(thm)], ['174'])).
% 25.42/25.67  thf('176', plain,
% 25.42/25.67      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 25.42/25.67        | (zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['169', '175'])).
% 25.42/25.67  thf('177', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 25.42/25.67      inference('simplify', [status(thm)], ['176'])).
% 25.42/25.67  thf('178', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('179', plain,
% 25.42/25.67      (((zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['177', '178'])).
% 25.42/25.67  thf('180', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('182', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('183', plain,
% 25.42/25.67      (((zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 25.42/25.67  thf('184', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (zip_tseitin_1 @ sk_B @ sk_C))),
% 25.42/25.67      inference('simplify', [status(thm)], ['183'])).
% 25.42/25.67  thf('185', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('186', plain,
% 25.42/25.67      (((zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['184', '185'])).
% 25.42/25.67  thf('187', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('188', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_D))),
% 25.42/25.67      inference('demod', [status(thm)], ['3', '4'])).
% 25.42/25.67  thf('189', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['187', '188'])).
% 25.42/25.67  thf('190', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_D)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['187', '188'])).
% 25.42/25.67  thf('191', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('192', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('193', plain,
% 25.42/25.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X19)
% 25.42/25.67          | ~ (m1_pre_topc @ X19 @ X20)
% 25.42/25.67          | (r1_tsep_1 @ X19 @ X21)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X20 @ X19 @ X21) @ X19)
% 25.42/25.67          | ~ (m1_pre_topc @ X21 @ X20)
% 25.42/25.67          | (v2_struct_0 @ X21)
% 25.42/25.67          | ~ (l1_pre_topc @ X20)
% 25.42/25.67          | ~ (v2_pre_topc @ X20)
% 25.42/25.67          | (v2_struct_0 @ X20))),
% 25.42/25.67      inference('cnf', [status(esa)], [t30_tsep_1])).
% 25.42/25.67  thf('194', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ sk_C)
% 25.42/25.67          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('sup-', [status(thm)], ['192', '193'])).
% 25.42/25.67  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('197', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ sk_C)
% 25.42/25.67          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('demod', [status(thm)], ['194', '195', '196'])).
% 25.42/25.67  thf('198', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_C)
% 25.42/25.67        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (v2_struct_0 @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['191', '197'])).
% 25.42/25.67  thf('199', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('200', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('201', plain,
% 25.42/25.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.67         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X3)
% 25.42/25.67          | ~ (l1_pre_topc @ X4)
% 25.42/25.67          | (v2_struct_0 @ X4)
% 25.42/25.67          | (v2_struct_0 @ X5)
% 25.42/25.67          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.67          | (m1_pre_topc @ (k2_tsep_1 @ X4 @ X3 @ X5) @ X4))),
% 25.42/25.67      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.67  thf('202', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('sup-', [status(thm)], ['200', '201'])).
% 25.42/25.67  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('204', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C))),
% 25.42/25.67      inference('demod', [status(thm)], ['202', '203'])).
% 25.42/25.67  thf('205', plain,
% 25.42/25.67      (((v2_struct_0 @ sk_C)
% 25.42/25.67        | (v2_struct_0 @ sk_A)
% 25.42/25.67        | (v2_struct_0 @ sk_B)
% 25.42/25.67        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ sk_A))),
% 25.42/25.67      inference('sup-', [status(thm)], ['199', '204'])).
% 25.42/25.67  thf('206', plain,
% 25.42/25.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 25.42/25.67         ((v2_struct_0 @ X15)
% 25.42/25.67          | ~ (m1_pre_topc @ X15 @ X16)
% 25.42/25.67          | (v2_struct_0 @ X17)
% 25.42/25.67          | ~ (m1_pre_topc @ X17 @ X16)
% 25.42/25.67          | (zip_tseitin_0 @ X17 @ X15)
% 25.42/25.67          | (zip_tseitin_1 @ X17 @ X18)
% 25.42/25.67          | ~ (m1_pre_topc @ X15 @ X18)
% 25.42/25.67          | ~ (m1_pre_topc @ X18 @ X16)
% 25.42/25.67          | (v2_struct_0 @ X18)
% 25.42/25.67          | ~ (l1_pre_topc @ X16)
% 25.42/25.67          | ~ (v2_pre_topc @ X16)
% 25.42/25.67          | (v2_struct_0 @ X16))),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.42/25.67  thf('207', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.67          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.67      inference('sup-', [status(thm)], ['205', '206'])).
% 25.42/25.67  thf('208', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.67  thf('210', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.67      inference('demod', [status(thm)], ['207', '208', '209'])).
% 25.42/25.67  thf('211', plain,
% 25.42/25.67      (![X0 : $i, X1 : $i]:
% 25.42/25.67         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.67          | (v2_struct_0 @ X1)
% 25.42/25.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.67          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.67          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ X0)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B))),
% 25.42/25.67      inference('simplify', [status(thm)], ['210'])).
% 25.42/25.67  thf('212', plain,
% 25.42/25.67      (![X0 : $i]:
% 25.42/25.67         ((v2_struct_0 @ sk_A)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.67          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.67          | (v2_struct_0 @ sk_C)
% 25.42/25.67          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 25.42/25.68          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.68          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['198', '211'])).
% 25.42/25.68  thf('213', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('214', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.68          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('demod', [status(thm)], ['212', '213'])).
% 25.42/25.68  thf('215', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | (zip_tseitin_1 @ X0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('simplify', [status(thm)], ['214'])).
% 25.42/25.68  thf('216', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['190', '215'])).
% 25.42/25.68  thf('217', plain,
% 25.42/25.68      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B))),
% 25.42/25.68      inference('simplify', [status(thm)], ['216'])).
% 25.42/25.68  thf('218', plain,
% 25.42/25.68      (![X11 : $i, X12 : $i]:
% 25.42/25.68         ((r1_tsep_1 @ X11 @ X12) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.42/25.68  thf('219', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_D @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['217', '218'])).
% 25.42/25.68  thf('220', plain,
% 25.42/25.68      (((m1_pre_topc @ sk_C @ sk_D)) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.68      inference('split', [status(esa)], ['94'])).
% 25.42/25.68  thf('221', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('222', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('223', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('224', plain,
% 25.42/25.68      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 25.42/25.68         ((v2_struct_0 @ X22)
% 25.42/25.68          | ~ (m1_pre_topc @ X22 @ X23)
% 25.42/25.68          | (v2_struct_0 @ X24)
% 25.42/25.68          | ~ (m1_pre_topc @ X24 @ X23)
% 25.42/25.68          | ~ (m1_pre_topc @ X22 @ X24)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ X23 @ X22 @ X25) @ 
% 25.42/25.68             (k2_tsep_1 @ X23 @ X24 @ X25))
% 25.42/25.68          | (r1_tsep_1 @ X22 @ X25)
% 25.42/25.68          | ~ (m1_pre_topc @ X25 @ X23)
% 25.42/25.68          | (v2_struct_0 @ X25)
% 25.42/25.68          | ~ (l1_pre_topc @ X23)
% 25.42/25.68          | ~ (v2_pre_topc @ X23)
% 25.42/25.68          | (v2_struct_0 @ X23))),
% 25.42/25.68      inference('cnf', [status(esa)], [t32_tmap_1])).
% 25.42/25.68  thf('225', plain,
% 25.42/25.68      (![X0 : $i, X1 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.68          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ X1 @ X0))
% 25.42/25.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 25.42/25.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X1)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('sup-', [status(thm)], ['223', '224'])).
% 25.42/25.68  thf('226', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('227', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('228', plain,
% 25.42/25.68      (![X0 : $i, X1 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ X1 @ X0))
% 25.42/25.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 25.42/25.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X1)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('demod', [status(thm)], ['225', '226', '227'])).
% 25.42/25.68  thf('229', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | ~ (m1_pre_topc @ sk_C @ X0)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ X0 @ sk_B))
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['222', '228'])).
% 25.42/25.68  thf('230', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('sup-', [status(thm)], ['221', '229'])).
% 25.42/25.68  thf('231', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68            (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['220', '230'])).
% 25.42/25.68  thf('232', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['199', '204'])).
% 25.42/25.68  thf('233', plain,
% 25.42/25.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.42/25.68         ((v2_struct_0 @ X8)
% 25.42/25.68          | ~ (m1_pre_topc @ X8 @ X9)
% 25.42/25.68          | ~ (m1_pre_topc @ X8 @ X10)
% 25.42/25.68          | ~ (r1_tsep_1 @ X8 @ X10)
% 25.42/25.68          | ~ (m1_pre_topc @ X10 @ X9)
% 25.42/25.68          | (v2_struct_0 @ X10)
% 25.42/25.68          | ~ (l1_pre_topc @ X9)
% 25.42/25.68          | ~ (v2_pre_topc @ X9)
% 25.42/25.68          | (v2_struct_0 @ X9))),
% 25.42/25.68      inference('cnf', [status(esa)], [t22_tmap_1])).
% 25.42/25.68  thf('234', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.68          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['232', '233'])).
% 25.42/25.68  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('237', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('demod', [status(thm)], ['234', '235', '236'])).
% 25.42/25.68  thf('238', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_B))),
% 25.42/25.68      inference('simplify', [status(thm)], ['237'])).
% 25.42/25.68  thf('239', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A)
% 25.42/25.68         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68              (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 25.42/25.68         <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['231', '238'])).
% 25.42/25.68  thf('240', plain,
% 25.42/25.68      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68              (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['239'])).
% 25.42/25.68  thf('241', plain,
% 25.42/25.68      (((zip_tseitin_1 @ sk_B @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['184', '185'])).
% 25.42/25.68  thf('242', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('243', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('demod', [status(thm)], ['202', '203'])).
% 25.42/25.68  thf('244', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['242', '243'])).
% 25.42/25.68  thf('245', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['242', '243'])).
% 25.42/25.68  thf('246', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('247', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('248', plain,
% 25.42/25.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 25.42/25.68         ((v2_struct_0 @ X19)
% 25.42/25.68          | ~ (m1_pre_topc @ X19 @ X20)
% 25.42/25.68          | (r1_tsep_1 @ X19 @ X21)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ X20 @ X19 @ X21) @ X21)
% 25.42/25.68          | ~ (m1_pre_topc @ X21 @ X20)
% 25.42/25.68          | (v2_struct_0 @ X21)
% 25.42/25.68          | ~ (l1_pre_topc @ X20)
% 25.42/25.68          | ~ (v2_pre_topc @ X20)
% 25.42/25.68          | (v2_struct_0 @ X20))),
% 25.42/25.68      inference('cnf', [status(esa)], [t30_tsep_1])).
% 25.42/25.68  thf('249', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.68          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ X0)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('sup-', [status(thm)], ['247', '248'])).
% 25.42/25.68  thf('250', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('251', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('252', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ X0)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('demod', [status(thm)], ['249', '250', '251'])).
% 25.42/25.68  thf('253', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_C)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['246', '252'])).
% 25.42/25.68  thf('254', plain,
% 25.42/25.68      (![X0 : $i, X1 : $i]:
% 25.42/25.68         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | (v2_struct_0 @ X1)
% 25.42/25.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.68          | (zip_tseitin_0 @ X1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | (zip_tseitin_1 @ X1 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_B))),
% 25.42/25.68      inference('simplify', [status(thm)], ['210'])).
% 25.42/25.68  thf('255', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 25.42/25.68          | (zip_tseitin_1 @ X0 @ sk_B)
% 25.42/25.68          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['253', '254'])).
% 25.42/25.68  thf('256', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('257', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (zip_tseitin_1 @ X0 @ sk_B)
% 25.42/25.68          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('demod', [status(thm)], ['255', '256'])).
% 25.42/25.68  thf('258', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (zip_tseitin_0 @ X0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | (zip_tseitin_1 @ X0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('simplify', [status(thm)], ['257'])).
% 25.42/25.68  thf('259', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['245', '258'])).
% 25.42/25.68  thf('260', plain,
% 25.42/25.68      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68        | (zip_tseitin_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D))),
% 25.42/25.68      inference('simplify', [status(thm)], ['259'])).
% 25.42/25.68  thf('261', plain,
% 25.42/25.68      (![X11 : $i, X12 : $i]:
% 25.42/25.68         ((r1_tsep_1 @ X11 @ X12) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.42/25.68  thf('262', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_C @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['260', '261'])).
% 25.42/25.68  thf('263', plain,
% 25.42/25.68      (((m1_pre_topc @ sk_B @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('split', [status(esa)], ['37'])).
% 25.42/25.68  thf('264', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('265', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('266', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('267', plain,
% 25.42/25.68      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 25.42/25.68         ((v2_struct_0 @ X22)
% 25.42/25.68          | ~ (m1_pre_topc @ X22 @ X23)
% 25.42/25.68          | (v2_struct_0 @ X24)
% 25.42/25.68          | ~ (m1_pre_topc @ X24 @ X23)
% 25.42/25.68          | ~ (m1_pre_topc @ X25 @ X24)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ X23 @ X22 @ X25) @ 
% 25.42/25.68             (k2_tsep_1 @ X23 @ X22 @ X24))
% 25.42/25.68          | (r1_tsep_1 @ X22 @ X25)
% 25.42/25.68          | ~ (m1_pre_topc @ X25 @ X23)
% 25.42/25.68          | (v2_struct_0 @ X25)
% 25.42/25.68          | ~ (l1_pre_topc @ X23)
% 25.42/25.68          | ~ (v2_pre_topc @ X23)
% 25.42/25.68          | (v2_struct_0 @ X23))),
% 25.42/25.68      inference('cnf', [status(esa)], [t32_tmap_1])).
% 25.42/25.68  thf('268', plain,
% 25.42/25.68      (![X0 : $i, X1 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | ~ (v2_pre_topc @ sk_A)
% 25.42/25.68          | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ sk_C @ X1))
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ X1)
% 25.42/25.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X1)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('sup-', [status(thm)], ['266', '267'])).
% 25.42/25.68  thf('269', plain, ((v2_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('270', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('271', plain,
% 25.42/25.68      (![X0 : $i, X1 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ X0)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ X0) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ sk_C @ X1))
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ X1)
% 25.42/25.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X1)
% 25.42/25.68          | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('demod', [status(thm)], ['268', '269', '270'])).
% 25.42/25.68  thf('272', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | ~ (m1_pre_topc @ sk_B @ X0)
% 25.42/25.68          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ sk_C @ X0))
% 25.42/25.68          | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_B)
% 25.42/25.68          | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('sup-', [status(thm)], ['265', '271'])).
% 25.42/25.68  thf('273', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68           (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68        | ~ (m1_pre_topc @ sk_B @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_C))),
% 25.42/25.68      inference('sup-', [status(thm)], ['264', '272'])).
% 25.42/25.68  thf('274', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68            (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['263', '273'])).
% 25.42/25.68  thf('275', plain,
% 25.42/25.68      (![X0 : $i]:
% 25.42/25.68         ((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ X0)
% 25.42/25.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ X0)
% 25.42/25.68          | (v2_struct_0 @ sk_C)
% 25.42/25.68          | (v2_struct_0 @ sk_A)
% 25.42/25.68          | (v2_struct_0 @ sk_B))),
% 25.42/25.68      inference('simplify', [status(thm)], ['237'])).
% 25.42/25.68  thf('276', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_A)
% 25.42/25.68         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68              (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 25.42/25.68         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['274', '275'])).
% 25.42/25.68  thf('277', plain,
% 25.42/25.68      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68              (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['276'])).
% 25.42/25.68  thf('278', plain,
% 25.42/25.68      ((((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 25.42/25.68         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['262', '277'])).
% 25.42/25.68  thf('279', plain,
% 25.42/25.68      (((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))))
% 25.42/25.68         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['278'])).
% 25.42/25.68  thf('280', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['244', '279'])).
% 25.42/25.68  thf('281', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['280'])).
% 25.42/25.68  thf('282', plain,
% 25.42/25.68      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 25.42/25.68      inference('split', [status(esa)], ['63'])).
% 25.42/25.68  thf('283', plain,
% 25.42/25.68      (![X13 : $i, X14 : $i]:
% 25.42/25.68         (~ (r1_tsep_1 @ X14 @ X13) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.42/25.68  thf('284', plain,
% 25.42/25.68      ((~ (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['282', '283'])).
% 25.42/25.68  thf('285', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D))
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['281', '284'])).
% 25.42/25.68  thf('286', plain,
% 25.42/25.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.68         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X3)
% 25.42/25.68          | ~ (l1_pre_topc @ X4)
% 25.42/25.68          | (v2_struct_0 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X5)
% 25.42/25.68          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.68          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.68      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.68  thf('287', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_C @ sk_A)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['285', '286'])).
% 25.42/25.68  thf('288', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('289', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('290', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('291', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('demod', [status(thm)], ['287', '288', '289', '290'])).
% 25.42/25.68  thf('292', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['291'])).
% 25.42/25.68  thf('293', plain,
% 25.42/25.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.68         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X3)
% 25.42/25.68          | ~ (l1_pre_topc @ X4)
% 25.42/25.68          | (v2_struct_0 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X5)
% 25.42/25.68          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.68          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.68      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.68  thf('294', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_C @ sk_A)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['292', '293'])).
% 25.42/25.68  thf('295', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('296', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('297', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('298', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('demod', [status(thm)], ['294', '295', '296', '297'])).
% 25.42/25.68  thf('299', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['298'])).
% 25.42/25.68  thf('300', plain,
% 25.42/25.68      (![X13 : $i, X14 : $i]:
% 25.42/25.68         (~ (r1_tsep_1 @ X13 @ X14) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.42/25.68  thf('301', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | ~ (zip_tseitin_1 @ sk_B @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['299', '300'])).
% 25.42/25.68  thf('302', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['241', '301'])).
% 25.42/25.68  thf('303', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['302'])).
% 25.42/25.68  thf('304', plain, (~ (v2_struct_0 @ sk_D)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('305', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['303', '304'])).
% 25.42/25.68  thf('306', plain, (~ (v2_struct_0 @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('307', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('clc', [status(thm)], ['305', '306'])).
% 25.42/25.68  thf('308', plain, (~ (v2_struct_0 @ sk_B)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('309', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_C))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 25.42/25.68             ((m1_pre_topc @ sk_B @ sk_D)))),
% 25.42/25.68      inference('clc', [status(thm)], ['307', '308'])).
% 25.42/25.68  thf('310', plain, (~ (v2_struct_0 @ sk_C)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('311', plain,
% 25.42/25.68      (~ ((m1_pre_topc @ sk_B @ sk_D)) | 
% 25.42/25.68       ~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 25.42/25.68      inference('sup-', [status(thm)], ['309', '310'])).
% 25.42/25.68  thf('312', plain,
% 25.42/25.68      (~ ((m1_pre_topc @ sk_B @ sk_D)) | 
% 25.42/25.68       ~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B))),
% 25.42/25.68      inference('sup-', [status(thm)], ['89', '90'])).
% 25.42/25.68  thf('313', plain,
% 25.42/25.68      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 25.42/25.68       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) | 
% 25.42/25.68       ((m1_pre_topc @ sk_C @ sk_D))),
% 25.42/25.68      inference('split', [status(esa)], ['94'])).
% 25.42/25.68  thf('314', plain, (((m1_pre_topc @ sk_C @ sk_D))),
% 25.42/25.68      inference('sat_resolution*', [status(thm)], ['311', '312', '93', '313'])).
% 25.42/25.68  thf('315', plain,
% 25.42/25.68      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | ~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B) @ 
% 25.42/25.68             (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A))),
% 25.42/25.68      inference('simpl_trail', [status(thm)], ['240', '314'])).
% 25.42/25.68  thf('316', plain,
% 25.42/25.68      (((v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['219', '315'])).
% 25.42/25.68  thf('317', plain,
% 25.42/25.68      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['316'])).
% 25.42/25.68  thf('318', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B))),
% 25.42/25.68      inference('sup-', [status(thm)], ['189', '317'])).
% 25.42/25.68  thf('319', plain,
% 25.42/25.68      (((r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68        | (v2_struct_0 @ sk_C)
% 25.42/25.68        | (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68        | (v2_struct_0 @ sk_D)
% 25.42/25.68        | (v2_struct_0 @ sk_A)
% 25.42/25.68        | (v2_struct_0 @ sk_B))),
% 25.42/25.68      inference('simplify', [status(thm)], ['318'])).
% 25.42/25.68  thf('320', plain,
% 25.42/25.68      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('split', [status(esa)], ['63'])).
% 25.42/25.68  thf('321', plain,
% 25.42/25.68      (![X13 : $i, X14 : $i]:
% 25.42/25.68         (~ (r1_tsep_1 @ X14 @ X13) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.42/25.68  thf('322', plain,
% 25.42/25.68      ((~ (zip_tseitin_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['320', '321'])).
% 25.42/25.68  thf('323', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['319', '322'])).
% 25.42/25.68  thf('324', plain,
% 25.42/25.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.68         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X3)
% 25.42/25.68          | ~ (l1_pre_topc @ X4)
% 25.42/25.68          | (v2_struct_0 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X5)
% 25.42/25.68          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.68          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.68      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.68  thf('325', plain,
% 25.42/25.68      ((((r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_D @ sk_A)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['323', '324'])).
% 25.42/25.68  thf('326', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('327', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('328', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('329', plain,
% 25.42/25.68      ((((r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('demod', [status(thm)], ['325', '326', '327', '328'])).
% 25.42/25.68  thf('330', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_B))
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['329'])).
% 25.42/25.68  thf('331', plain,
% 25.42/25.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 25.42/25.68         (~ (m1_pre_topc @ X3 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X3)
% 25.42/25.68          | ~ (l1_pre_topc @ X4)
% 25.42/25.68          | (v2_struct_0 @ X4)
% 25.42/25.68          | (v2_struct_0 @ X5)
% 25.42/25.68          | ~ (m1_pre_topc @ X5 @ X4)
% 25.42/25.68          | ~ (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5)))),
% 25.42/25.68      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 25.42/25.68  thf('332', plain,
% 25.42/25.68      ((((r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | ~ (l1_pre_topc @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | ~ (m1_pre_topc @ sk_C @ sk_A)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['330', '331'])).
% 25.42/25.68  thf('333', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('334', plain, ((l1_pre_topc @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('335', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('336', plain,
% 25.42/25.68      ((((r1_tsep_1 @ sk_C @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('demod', [status(thm)], ['332', '333', '334', '335'])).
% 25.42/25.68  thf('337', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (r1_tsep_1 @ sk_C @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['336'])).
% 25.42/25.68  thf('338', plain,
% 25.42/25.68      (![X13 : $i, X14 : $i]:
% 25.42/25.68         (~ (r1_tsep_1 @ X13 @ X14) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 25.42/25.68  thf('339', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | ~ (zip_tseitin_1 @ sk_B @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['337', '338'])).
% 25.42/25.68  thf('340', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_A)
% 25.42/25.68         | (v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['186', '339'])).
% 25.42/25.68  thf('341', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_D)
% 25.42/25.68         | (v2_struct_0 @ sk_B)
% 25.42/25.68         | (v2_struct_0 @ sk_C)
% 25.42/25.68         | (v2_struct_0 @ sk_A)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('simplify', [status(thm)], ['340'])).
% 25.42/25.68  thf('342', plain, (~ (v2_struct_0 @ sk_D)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('343', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('sup-', [status(thm)], ['341', '342'])).
% 25.42/25.68  thf('344', plain, (~ (v2_struct_0 @ sk_A)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('345', plain,
% 25.42/25.68      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('clc', [status(thm)], ['343', '344'])).
% 25.42/25.68  thf('346', plain, (~ (v2_struct_0 @ sk_B)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('347', plain,
% 25.42/25.68      (((v2_struct_0 @ sk_C))
% 25.42/25.68         <= (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)))),
% 25.42/25.68      inference('clc', [status(thm)], ['345', '346'])).
% 25.42/25.68  thf('348', plain, (~ (v2_struct_0 @ sk_C)),
% 25.42/25.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.42/25.68  thf('349', plain,
% 25.42/25.68      (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C))),
% 25.42/25.68      inference('sup-', [status(thm)], ['347', '348'])).
% 25.42/25.68  thf('350', plain,
% 25.42/25.68      (((m1_pre_topc @ sk_B @ sk_D)) | 
% 25.42/25.68       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C)) | 
% 25.42/25.68       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))),
% 25.42/25.68      inference('split', [status(esa)], ['37'])).
% 25.42/25.68  thf('351', plain,
% 25.42/25.68      (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 25.42/25.68       ~ ((m1_pre_topc @ sk_B @ sk_D))),
% 25.42/25.68      inference('sup-', [status(thm)], ['309', '310'])).
% 25.42/25.68  thf('352', plain,
% 25.42/25.68      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 25.42/25.68       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_C) @ sk_B)) | 
% 25.42/25.68       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)) | 
% 25.42/25.68       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_B) @ sk_C))),
% 25.42/25.68      inference('split', [status(esa)], ['63'])).
% 25.42/25.68  thf('353', plain, ($false),
% 25.42/25.68      inference('sat_resolution*', [status(thm)],
% 25.42/25.68                ['91', '93', '95', '163', '349', '350', '351', '352'])).
% 25.42/25.68  
% 25.42/25.68  % SZS output end Refutation
% 25.42/25.68  
% 25.42/25.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
