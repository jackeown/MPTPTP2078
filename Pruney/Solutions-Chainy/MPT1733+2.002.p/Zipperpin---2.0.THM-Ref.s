%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mAtC8S7699

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:34 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 447 expanded)
%              Number of leaves         :   12 ( 120 expanded)
%              Depth                    :   22
%              Number of atoms          : 1309 (12697 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t42_tmap_1,conjecture,(
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
                   => ( ( ( ( r1_tsep_1 @ B @ D )
                          | ( r1_tsep_1 @ C @ D ) )
                       => ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) )
                      & ( ( ( r1_tsep_1 @ D @ B )
                          | ( r1_tsep_1 @ D @ C ) )
                       => ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) )).

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
                     => ( ( ( ( r1_tsep_1 @ B @ D )
                            | ( r1_tsep_1 @ C @ D ) )
                         => ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) )
                        & ( ( ( r1_tsep_1 @ D @ B )
                            | ( r1_tsep_1 @ D @ C ) )
                         => ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tmap_1])).

thf('0',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tmap_1,axiom,(
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
                   => ( ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D )
                       => ( ~ ( r1_tsep_1 @ B @ D )
                          & ~ ( r1_tsep_1 @ C @ D ) ) )
                      & ( ~ ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) )
                       => ( ~ ( r1_tsep_1 @ D @ B )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ X1 @ X0 @ X3 ) @ X2 )
      | ~ ( r1_tsep_1 @ X3 @ X2 )
      | ( r1_tsep_1 @ X0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t41_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ X0 @ X1 )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ X0 @ X1 )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( r1_tsep_1 @ X2 @ ( k2_tsep_1 @ X1 @ X0 @ X3 ) )
      | ~ ( r1_tsep_1 @ X2 @ X0 )
      | ( r1_tsep_1 @ X0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t41_tmap_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ sk_B )
      | ( r1_tsep_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ sk_B )
      | ( r1_tsep_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['13'])).

thf('40',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ X1 @ X0 @ X3 ) @ X2 )
      | ~ ( r1_tsep_1 @ X0 @ X2 )
      | ( r1_tsep_1 @ X0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t41_tmap_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ sk_B @ X1 )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ sk_B @ X1 )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('65',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('66',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['39','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['38','68'])).

thf('70',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( r1_tsep_1 @ X2 @ ( k2_tsep_1 @ X1 @ X0 @ X3 ) )
      | ~ ( r1_tsep_1 @ X2 @ X3 )
      | ( r1_tsep_1 @ X0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t41_tmap_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ X0 )
      | ( r1_tsep_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ X0 )
      | ( r1_tsep_1 @ X1 @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ X0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tsep_1 @ X0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['39','67'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('106',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['25','79','103','104','105','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mAtC8S7699
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 142 iterations in 0.087s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(t42_tmap_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.55                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.36/0.55                     ( ( ( ( r1_tsep_1 @ B @ D ) | ( r1_tsep_1 @ C @ D ) ) =>
% 0.36/0.55                         ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 0.36/0.55                       ( ( ( r1_tsep_1 @ D @ B ) | ( r1_tsep_1 @ D @ C ) ) =>
% 0.36/0.55                         ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55                  ( ![D:$i]:
% 0.36/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.55                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.36/0.55                        ( ( ( ( r1_tsep_1 @ B @ D ) | ( r1_tsep_1 @ C @ D ) ) =>
% 0.36/0.55                            ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 0.36/0.55                          ( ( ( r1_tsep_1 @ D @ B ) | ( r1_tsep_1 @ D @ C ) ) =>
% 0.36/0.55                            ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t42_tmap_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_C @ sk_D)
% 0.36/0.55        | (r1_tsep_1 @ sk_B @ sk_D)
% 0.36/0.55        | ~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t41_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.55                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.36/0.55                     ( ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) =>
% 0.36/0.55                         ( ( ~( r1_tsep_1 @ B @ D ) ) & 
% 0.36/0.55                           ( ~( r1_tsep_1 @ C @ D ) ) ) ) & 
% 0.36/0.55                       ( ( ~( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.36/0.55                         ( ( ~( r1_tsep_1 @ D @ B ) ) & 
% 0.36/0.55                           ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.55          | (v2_struct_0 @ X2)
% 0.36/0.55          | ~ (m1_pre_topc @ X2 @ X1)
% 0.36/0.55          | (r1_tsep_1 @ (k2_tsep_1 @ X1 @ X0 @ X3) @ X2)
% 0.36/0.55          | ~ (r1_tsep_1 @ X3 @ X2)
% 0.36/0.55          | (r1_tsep_1 @ X0 @ X3)
% 0.36/0.55          | ~ (m1_pre_topc @ X3 @ X1)
% 0.36/0.55          | (v2_struct_0 @ X3)
% 0.36/0.55          | ~ (l1_pre_topc @ X1)
% 0.36/0.55          | ~ (v2_pre_topc @ X1)
% 0.36/0.55          | (v2_struct_0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [t41_tmap_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.55          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.55          | ~ (r1_tsep_1 @ X0 @ X1)
% 0.36/0.55          | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X1)
% 0.36/0.55          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ X1)
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.55          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.55          | ~ (r1_tsep_1 @ X0 @ X1)
% 0.36/0.55          | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X1)
% 0.36/0.55          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ X1)
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.55          | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 0.36/0.55          | ~ (r1_tsep_1 @ sk_C @ X0)
% 0.36/0.55          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.55          | (v2_struct_0 @ sk_C)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_C)
% 0.36/0.55        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.55        | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.36/0.55        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '10'])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B)
% 0.36/0.55         | (v2_struct_0 @ sk_D)
% 0.36/0.55         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.36/0.55         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.55         | (v2_struct_0 @ sk_C)
% 0.36/0.55         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.36/0.55        | ~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 0.36/0.55         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.36/0.55      inference('split', [status(esa)], ['13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_A)
% 0.36/0.55         | (v2_struct_0 @ sk_C)
% 0.36/0.55         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.55         | (v2_struct_0 @ sk_D)
% 0.36/0.55         | (v2_struct_0 @ sk_B)))
% 0.36/0.55         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.55             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.55  thf('16', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B)
% 0.36/0.55         | (v2_struct_0 @ sk_D)
% 0.36/0.55         | (v2_struct_0 @ sk_C)
% 0.36/0.55         | (v2_struct_0 @ sk_A)))
% 0.36/0.55         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.55             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf('18', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.36/0.55         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.55             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.36/0.55         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.55             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C))
% 0.36/0.55         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.55             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.36/0.55      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.36/0.55       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.36/0.55        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.36/0.55        | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.55      inference('split', [status(esa)], ['26'])).
% 0.36/0.55  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('29', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ X2)
% 0.36/0.56          | ~ (m1_pre_topc @ X2 @ X1)
% 0.36/0.56          | (r1_tsep_1 @ X2 @ (k2_tsep_1 @ X1 @ X0 @ X3))
% 0.36/0.56          | ~ (r1_tsep_1 @ X2 @ X0)
% 0.36/0.56          | (r1_tsep_1 @ X0 @ X3)
% 0.36/0.56          | ~ (m1_pre_topc @ X3 @ X1)
% 0.36/0.56          | (v2_struct_0 @ X3)
% 0.36/0.56          | ~ (l1_pre_topc @ X1)
% 0.36/0.56          | ~ (v2_pre_topc @ X1)
% 0.36/0.56          | (v2_struct_0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [t41_tmap_1])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ X1 @ sk_B)
% 0.36/0.56          | (r1_tsep_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.56  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ X1 @ sk_B)
% 0.36/0.56          | (r1_tsep_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_B)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.36/0.56          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56          | (v2_struct_0 @ sk_C)
% 0.36/0.56          | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '35'])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_A)
% 0.36/0.56        | (v2_struct_0 @ sk_C)
% 0.36/0.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 0.36/0.56        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.36/0.56        | (v2_struct_0 @ sk_D)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['28', '36'])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.36/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '37'])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      ((~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.36/0.56      inference('split', [status(esa)], ['13'])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ X2)
% 0.36/0.56          | ~ (m1_pre_topc @ X2 @ X1)
% 0.36/0.56          | (r1_tsep_1 @ (k2_tsep_1 @ X1 @ X0 @ X3) @ X2)
% 0.36/0.56          | ~ (r1_tsep_1 @ X0 @ X2)
% 0.36/0.56          | (r1_tsep_1 @ X0 @ X3)
% 0.36/0.56          | ~ (m1_pre_topc @ X3 @ X1)
% 0.36/0.56          | (v2_struct_0 @ X3)
% 0.36/0.56          | ~ (l1_pre_topc @ X1)
% 0.36/0.56          | ~ (v2_pre_topc @ X1)
% 0.36/0.56          | (v2_struct_0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [t41_tmap_1])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ sk_B @ X1)
% 0.36/0.56          | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X1)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ sk_B @ X1)
% 0.36/0.56          | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X1)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_B)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56          | (v2_struct_0 @ sk_C)
% 0.36/0.56          | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['42', '48'])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_A)
% 0.36/0.56        | (v2_struct_0 @ sk_C)
% 0.36/0.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 0.36/0.56        | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.36/0.56        | (v2_struct_0 @ sk_D)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['41', '49'])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.36/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['40', '50'])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.36/0.56      inference('split', [status(esa)], ['13'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_B)))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.56             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.56  thf('54', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.56             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.56  thf('56', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.56             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.56  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.56             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('clc', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_C))
% 0.36/0.56         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.36/0.56             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.36/0.56      inference('clc', [status(thm)], ['59', '60'])).
% 0.36/0.56  thf('62', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.36/0.56       ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.36/0.56       ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.36/0.56       ~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.36/0.56      inference('split', [status(esa)], ['13'])).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (((r1_tsep_1 @ sk_B @ sk_D)) | ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.36/0.56       ~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('67', plain, (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['63', '64', '65', '66'])).
% 0.36/0.56  thf('68', plain, (~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['39', '67'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['38', '68'])).
% 0.36/0.56  thf('70', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.56  thf('72', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.36/0.56         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.56  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.36/0.56         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.36/0.56  thf('76', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('77', plain, (((v2_struct_0 @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.36/0.56      inference('clc', [status(thm)], ['75', '76'])).
% 0.36/0.56  thf('78', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('79', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('split', [status(esa)], ['26'])).
% 0.36/0.56  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('82', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('83', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ X2)
% 0.36/0.56          | ~ (m1_pre_topc @ X2 @ X1)
% 0.36/0.56          | (r1_tsep_1 @ X2 @ (k2_tsep_1 @ X1 @ X0 @ X3))
% 0.36/0.56          | ~ (r1_tsep_1 @ X2 @ X3)
% 0.36/0.56          | (r1_tsep_1 @ X0 @ X3)
% 0.36/0.56          | ~ (m1_pre_topc @ X3 @ X1)
% 0.36/0.56          | (v2_struct_0 @ X3)
% 0.36/0.56          | ~ (l1_pre_topc @ X1)
% 0.36/0.56          | ~ (v2_pre_topc @ X1)
% 0.36/0.56          | (v2_struct_0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [t41_tmap_1])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ X1 @ X0)
% 0.36/0.56          | (r1_tsep_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.56  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.36/0.56          | ~ (r1_tsep_1 @ X1 @ X0)
% 0.36/0.56          | (r1_tsep_1 @ X1 @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_B)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (r1_tsep_1 @ X0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.36/0.56          | ~ (r1_tsep_1 @ X0 @ sk_C)
% 0.36/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56          | (v2_struct_0 @ sk_C)
% 0.36/0.56          | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['82', '88'])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_A)
% 0.36/0.56        | (v2_struct_0 @ sk_C)
% 0.36/0.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 0.36/0.56        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.36/0.56        | (v2_struct_0 @ sk_D)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['81', '89'])).
% 0.36/0.56  thf('91', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.36/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['80', '90'])).
% 0.36/0.56  thf('92', plain, (~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['39', '67'])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['91', '92'])).
% 0.36/0.56  thf('94', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('95', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_C)
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.56  thf('96', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('97', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.36/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.56  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.36/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('clc', [status(thm)], ['97', '98'])).
% 0.36/0.56  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('101', plain, (((v2_struct_0 @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.36/0.56      inference('clc', [status(thm)], ['99', '100'])).
% 0.36/0.56  thf('102', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('103', plain, (~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.36/0.56      inference('sup-', [status(thm)], ['101', '102'])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.36/0.56       ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.36/0.56      inference('split', [status(esa)], ['26'])).
% 0.36/0.56  thf('105', plain,
% 0.36/0.56      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 0.36/0.56       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.36/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.56  thf('106', plain,
% 0.36/0.56      (((r1_tsep_1 @ sk_C @ sk_D)
% 0.36/0.56        | (r1_tsep_1 @ sk_B @ sk_D)
% 0.36/0.56        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.36/0.56        | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('107', plain,
% 0.36/0.56      (((r1_tsep_1 @ sk_B @ sk_D)) | ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.36/0.56       ((r1_tsep_1 @ sk_D @ sk_B)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.36/0.56      inference('split', [status(esa)], ['106'])).
% 0.36/0.56  thf('108', plain, ($false),
% 0.36/0.56      inference('sat_resolution*', [status(thm)],
% 0.36/0.56                ['25', '79', '103', '104', '105', '107'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
