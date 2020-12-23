%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qOyM3XRm5M

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 569 expanded)
%              Number of leaves         :   12 ( 157 expanded)
%              Depth                    :   21
%              Number of atoms          : 1940 (22899 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)

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

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t40_tmap_1,conjecture,(
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
                 => ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                     => ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ C @ D ) ) )
                    & ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ C @ D ) )
                     => ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                    & ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                     => ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ D @ C ) ) )
                    & ( ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ D @ C ) )
                     => ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) )).

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
                   => ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                       => ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ C @ D ) ) )
                      & ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ C @ D ) )
                       => ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                      & ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                       => ( ( r1_tsep_1 @ D @ B )
                          & ( r1_tsep_1 @ D @ C ) ) )
                      & ( ( ( r1_tsep_1 @ D @ B )
                          & ( r1_tsep_1 @ D @ C ) )
                       => ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_tmap_1])).

thf('0',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['10'])).

thf('15',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ X3 @ X2 )
      | ~ ( r1_tsep_1 @ X0 @ X2 )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( r1_tsep_1 @ sk_B @ X1 )
      | ~ ( r1_tsep_1 @ X0 @ X1 )
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
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( r1_tsep_1 @ sk_B @ X1 )
      | ~ ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tsep_1 @ sk_C @ sk_D )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['27'])).

thf('39',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['10'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) @ X2 )
      | ( r1_tsep_1 @ X3 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('48',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['27'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('59',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ X2 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ( r1_tsep_1 @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66'])).

thf('68',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['27'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ X2 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ( r1_tsep_1 @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85'])).

thf('87',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['10'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) @ X2 )
      | ( r1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['27'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('119',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('120',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ X2 @ X3 )
      | ~ ( r1_tsep_1 @ X2 @ X0 )
      | ( r1_tsep_1 @ X2 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_tmap_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_tsep_1 @ X1 @ sk_B )
      | ~ ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tsep_1 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_tsep_1 @ X1 @ sk_B )
      | ~ ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_C )
      | ~ ( r1_tsep_1 @ X0 @ sk_B )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tsep_1 @ sk_D @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['119','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','130'])).

thf('132',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['27'])).

thf('133',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('134',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('135',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('136',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('137',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('138',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['133','134','38','135','136','77','96','137'])).

thf('139',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['132','138'])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','37','38','57','58','77','96','115','117','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qOyM3XRm5M
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 204 iterations in 0.057s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(t40_tmap_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                   ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) =>
% 0.20/0.52                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 0.20/0.52                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) =>
% 0.20/0.52                       ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 0.20/0.52                     ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) =>
% 0.20/0.52                       ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 0.20/0.52                     ( ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) =>
% 0.20/0.52                       ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                      ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) =>
% 0.20/0.52                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 0.20/0.52                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) =>
% 0.20/0.52                          ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 0.20/0.52                        ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) =>
% 0.20/0.52                          ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 0.20/0.52                        ( ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) =>
% 0.20/0.52                          ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t40_tmap_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_C)) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_B)) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_C)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_C @ sk_D)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_B)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_C @ sk_D)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('15', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t39_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                   ( ( ~( ( ~( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 0.20/0.52                          ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 0.20/0.52                     ( ~( ( ~( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 0.20/0.52                          ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) ) & 
% 0.20/0.52                     ( ~( ( ~( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.20/0.52                          ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 0.20/0.52                     ( ~( ( ~( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 0.20/0.52                          ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ X3 @ X2)
% 0.20/0.52          | ~ (r1_tsep_1 @ X0 @ X2)
% 0.20/0.52          | (r1_tsep_1 @ (k1_tsep_1 @ X1 @ X0 @ X3) @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X3 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_tmap_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ sk_B @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ X0 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ sk_B @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ X0 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (r1_tsep_1 @ sk_C @ X0)
% 0.20/0.52          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.20/0.52          | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_C)
% 0.20/0.52        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52         | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.52  thf('30', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ sk_C)) | ~ ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 0.20/0.52         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ (k1_tsep_1 @ X1 @ X0 @ X3) @ X2)
% 0.20/0.52          | (r1_tsep_1 @ X3 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X3 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_tmap_1])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.52         | (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_C @ sk_D)) <= (~ ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_C @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ X2 @ (k1_tsep_1 @ X1 @ X0 @ X3))
% 0.20/0.52          | (r1_tsep_1 @ X2 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X3 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_tmap_1])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.52         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('65', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_B)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ X2 @ (k1_tsep_1 @ X1 @ X0 @ X3))
% 0.20/0.52          | (r1_tsep_1 @ X2 @ X3)
% 0.20/0.52          | ~ (m1_pre_topc @ X3 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_tmap_1])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.52         | (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.52  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['80', '81', '82', '83', '84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_D @ sk_C)) <= (~ ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.52  thf('89', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.52  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.52  thf('93', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 0.20/0.52             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.52  thf('95', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_C)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 0.20/0.52         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ (k1_tsep_1 @ X1 @ X0 @ X3) @ X2)
% 0.20/0.52          | (r1_tsep_1 @ X0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X3 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_tmap_1])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.52         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.52  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('103', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('104', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['99', '100', '101', '102', '103', '104'])).
% 0.20/0.52  thf('106', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.52  thf('108', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.52  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['109', '110'])).
% 0.20/0.52  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 0.20/0.52             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['111', '112'])).
% 0.20/0.52  thf('114', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('115', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.52  thf('116', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('117', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_B)) | ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['116'])).
% 0.20/0.52  thf('118', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('119', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('120', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('121', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('122', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('123', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (r1_tsep_1 @ X2 @ X3)
% 0.20/0.52          | ~ (r1_tsep_1 @ X2 @ X0)
% 0.20/0.52          | (r1_tsep_1 @ X2 @ (k1_tsep_1 @ X1 @ X0 @ X3))
% 0.20/0.52          | ~ (m1_pre_topc @ X3 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X3)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_tmap_1])).
% 0.20/0.52  thf('124', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (r1_tsep_1 @ X1 @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 0.20/0.52          | ~ (r1_tsep_1 @ X1 @ sk_B)
% 0.20/0.52          | ~ (r1_tsep_1 @ X1 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.52  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('127', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (r1_tsep_1 @ X1 @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 0.20/0.52          | ~ (r1_tsep_1 @ X1 @ sk_B)
% 0.20/0.52          | ~ (r1_tsep_1 @ X1 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.20/0.52  thf('128', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (r1_tsep_1 @ X0 @ sk_C)
% 0.20/0.52          | ~ (r1_tsep_1 @ X0 @ sk_B)
% 0.20/0.52          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52          | (v2_struct_0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['121', '127'])).
% 0.20/0.52  thf('129', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_C)
% 0.20/0.52        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.52        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['120', '128'])).
% 0.20/0.52  thf('130', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['119', '129'])).
% 0.20/0.52  thf('131', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['118', '130'])).
% 0.20/0.52  thf('132', plain,
% 0.20/0.52      ((~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.52         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['27'])).
% 0.20/0.52  thf('133', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('134', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('135', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('136', plain,
% 0.20/0.52      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 0.20/0.52       ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['12'])).
% 0.20/0.52  thf('137', plain,
% 0.20/0.52      (((r1_tsep_1 @ sk_B @ sk_D)) | 
% 0.20/0.52       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.52  thf('138', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)],
% 0.20/0.52                ['133', '134', '38', '135', '136', '77', '96', '137'])).
% 0.20/0.52  thf('139', plain, (~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['132', '138'])).
% 0.20/0.52  thf('140', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_C)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['131', '139'])).
% 0.20/0.52  thf('141', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('142', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['140', '141'])).
% 0.20/0.52  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('144', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('clc', [status(thm)], ['142', '143'])).
% 0.20/0.52  thf('145', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('146', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C))
% 0.20/0.52         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.52      inference('clc', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('147', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('148', plain,
% 0.20/0.52      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['146', '147'])).
% 0.20/0.52  thf('149', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)],
% 0.20/0.52                ['1', '3', '5', '7', '9', '11', '37', '38', '57', '58', '77', 
% 0.20/0.52                 '96', '115', '117', '148'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
