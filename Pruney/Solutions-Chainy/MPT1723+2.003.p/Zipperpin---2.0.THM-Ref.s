%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qc09jrJuSU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 336 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   31
%              Number of atoms          : 1415 (9383 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t32_tmap_1,conjecture,(
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
                         => ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ D @ C ) ) )
                        & ( ( m1_pre_topc @ C @ D )
                         => ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_tmap_1])).

thf('0',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( ( k1_tsep_1 @ X4 @ X3 @ X3 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t23_tsep_1,axiom,(
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
              <=> ( ( k1_tsep_1 @ A @ B @ C )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( k1_tsep_1 @ X1 @ X0 @ X2 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tsep_1 @ X1 @ X0 @ sk_C )
       != ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tmap_1,axiom,(
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
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ B @ D )
                          & ( m1_pre_topc @ C @ E ) )
                       => ( ( r1_tsep_1 @ B @ C )
                          | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X7 )
      | ( r1_tsep_1 @ X5 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X8 ) @ ( k2_tsep_1 @ X6 @ X7 @ X9 ) )
      | ~ ( m1_pre_topc @ X9 @ X6 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_tmap_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( ( k1_tsep_1 @ X4 @ X3 @ X3 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( k1_tsep_1 @ X1 @ X0 @ X2 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tsep_1 @ X1 @ X0 @ sk_B )
       != ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['46','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['41'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['43','45','88'])).

thf('90',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['42','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['40','90'])).

thf('92',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ~ ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['24'])).

thf('103',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','101','102','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qc09jrJuSU
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 88 iterations in 0.057s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.19/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.51  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.19/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.51  thf(t32_tmap_1, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51               ( ![D:$i]:
% 0.19/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.51                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.19/0.51                     ( ( ( m1_pre_topc @ B @ D ) =>
% 0.19/0.51                         ( m1_pre_topc @
% 0.19/0.51                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.19/0.51                           ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 0.19/0.51                       ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.51                         ( m1_pre_topc @
% 0.19/0.51                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.19/0.51                           ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51            ( l1_pre_topc @ A ) ) =>
% 0.19/0.51          ( ![B:$i]:
% 0.19/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51              ( ![C:$i]:
% 0.19/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51                  ( ![D:$i]:
% 0.19/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.51                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.19/0.51                        ( ( ( m1_pre_topc @ B @ D ) =>
% 0.19/0.51                            ( m1_pre_topc @
% 0.19/0.51                              ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.19/0.51                              ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 0.19/0.51                          ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.51                            ( m1_pre_topc @
% 0.19/0.51                              ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.19/0.51                              ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t32_tmap_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (((m1_pre_topc @ sk_B @ sk_D) | (m1_pre_topc @ sk_C @ sk_D))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (((m1_pre_topc @ sk_C @ sk_D)) | ((m1_pre_topc @ sk_B @ sk_D))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t25_tmap_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.19/0.51             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X3 : $i, X4 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X3)
% 0.19/0.51          | ~ (m1_pre_topc @ X3 @ X4)
% 0.19/0.51          | ((k1_tsep_1 @ X4 @ X3 @ X3)
% 0.19/0.51              = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.19/0.51          | ~ (l1_pre_topc @ X4)
% 0.19/0.51          | ~ (v2_pre_topc @ X4)
% 0.19/0.51          | (v2_struct_0 @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.19/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.19/0.51        | (v2_struct_0 @ sk_C))),
% 0.19/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.19/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.19/0.51        | (v2_struct_0 @ sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.51  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_C)
% 0.19/0.51        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.19/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.19/0.51      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf('10', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.19/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.19/0.51      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf(t23_tsep_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51               ( ( m1_pre_topc @ B @ C ) <=>
% 0.19/0.51                 ( ( k1_tsep_1 @ A @ B @ C ) =
% 0.19/0.51                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.51          | ((k1_tsep_1 @ X1 @ X0 @ X2)
% 0.19/0.51              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.19/0.51          | (m1_pre_topc @ X0 @ X2)
% 0.19/0.51          | ~ (m1_pre_topc @ X2 @ X1)
% 0.19/0.51          | (v2_struct_0 @ X2)
% 0.19/0.51          | ~ (l1_pre_topc @ X1)
% 0.19/0.51          | ~ (v2_pre_topc @ X1)
% 0.19/0.51          | (v2_struct_0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [t23_tsep_1])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_tsep_1 @ X1 @ X0 @ sk_C) != (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.19/0.51          | (v2_struct_0 @ X1)
% 0.19/0.51          | ~ (v2_pre_topc @ X1)
% 0.19/0.51          | ~ (l1_pre_topc @ X1)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.19/0.51          | (m1_pre_topc @ X0 @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.51          | (v2_struct_0 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_C)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.19/0.51        | (m1_pre_topc @ sk_C @ sk_C)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_C)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('eq_res', [status(thm)], ['13'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (m1_pre_topc @ sk_C @ sk_C)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_C))),
% 0.19/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.51  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (m1_pre_topc @ sk_C @ sk_C)
% 0.19/0.51        | (v2_struct_0 @ sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.19/0.51  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('21', plain, (((v2_struct_0 @ sk_C) | (m1_pre_topc @ sk_C @ sk_C))),
% 0.19/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.19/0.51  thf('22', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('23', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.19/0.51      inference('clc', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (((m1_pre_topc @ sk_B @ sk_D)
% 0.19/0.51        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (((m1_pre_topc @ sk_B @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['24'])).
% 0.19/0.51  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t28_tmap_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51               ( ![D:$i]:
% 0.19/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.51                   ( ![E:$i]:
% 0.19/0.51                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.19/0.51                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 0.19/0.51                         ( ( r1_tsep_1 @ B @ C ) | 
% 0.19/0.51                           ( m1_pre_topc @
% 0.19/0.51                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.19/0.51                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X5)
% 0.19/0.51          | ~ (m1_pre_topc @ X5 @ X6)
% 0.19/0.51          | (v2_struct_0 @ X7)
% 0.19/0.51          | ~ (m1_pre_topc @ X7 @ X6)
% 0.19/0.51          | ~ (m1_pre_topc @ X5 @ X7)
% 0.19/0.51          | (r1_tsep_1 @ X5 @ X8)
% 0.19/0.51          | ~ (m1_pre_topc @ X8 @ X9)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X8) @ 
% 0.19/0.51             (k2_tsep_1 @ X6 @ X7 @ X9))
% 0.19/0.51          | ~ (m1_pre_topc @ X9 @ X6)
% 0.19/0.51          | (v2_struct_0 @ X9)
% 0.19/0.51          | ~ (m1_pre_topc @ X8 @ X6)
% 0.19/0.51          | (v2_struct_0 @ X8)
% 0.19/0.51          | ~ (l1_pre_topc @ X6)
% 0.19/0.51          | ~ (v2_pre_topc @ X6)
% 0.19/0.51          | (v2_struct_0 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [t28_tmap_1])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X1)
% 0.19/0.51          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.19/0.51          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X2)
% 0.19/0.51          | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X1)
% 0.19/0.51          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.19/0.51          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X2)
% 0.19/0.51          | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_B)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.19/0.51          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X1)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['27', '33'])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 0.19/0.51          | (v2_struct_0 @ sk_D)
% 0.19/0.51          | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['26', '34'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          ((v2_struct_0 @ sk_B)
% 0.19/0.51           | (v2_struct_0 @ sk_D)
% 0.19/0.51           | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.51           | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51              (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.19/0.51           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51           | (v2_struct_0 @ X0)
% 0.19/0.51           | (v2_struct_0 @ sk_C)
% 0.19/0.51           | (v2_struct_0 @ sk_A)))
% 0.19/0.51         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['25', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_A)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.19/0.51         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '36'])).
% 0.19/0.51  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_A)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_B)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.19/0.51        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51           (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_D @ sk_C))))),
% 0.19/0.51      inference('split', [status(esa)], ['41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (~
% 0.19/0.51       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51         (k2_tsep_1 @ sk_A @ sk_D @ sk_C))) | 
% 0.19/0.51       ~
% 0.19/0.51       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51         (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['41'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.19/0.51        | (m1_pre_topc @ sk_C @ sk_D))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (((m1_pre_topc @ sk_C @ sk_D)) | 
% 0.19/0.51       ~
% 0.19/0.51       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51         (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 0.19/0.51      inference('split', [status(esa)], ['44'])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (((m1_pre_topc @ sk_C @ sk_D)) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['44'])).
% 0.19/0.51  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_B)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.19/0.51          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X1)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['27', '33'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.19/0.51          | (v2_struct_0 @ sk_B)
% 0.19/0.51          | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (![X3 : $i, X4 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X3)
% 0.19/0.51          | ~ (m1_pre_topc @ X3 @ X4)
% 0.19/0.51          | ((k1_tsep_1 @ X4 @ X3 @ X3)
% 0.19/0.51              = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.19/0.51          | ~ (l1_pre_topc @ X4)
% 0.19/0.51          | ~ (v2_pre_topc @ X4)
% 0.19/0.51          | (v2_struct_0 @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.19/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.19/0.51        | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.51  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.19/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.19/0.51        | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.19/0.51  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_B)
% 0.19/0.51        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.19/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.19/0.51      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 0.19/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.19/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.51          | ((k1_tsep_1 @ X1 @ X0 @ X2)
% 0.19/0.51              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.19/0.51          | (m1_pre_topc @ X0 @ X2)
% 0.19/0.51          | ~ (m1_pre_topc @ X2 @ X1)
% 0.19/0.51          | (v2_struct_0 @ X2)
% 0.19/0.51          | ~ (l1_pre_topc @ X1)
% 0.19/0.51          | ~ (v2_pre_topc @ X1)
% 0.19/0.51          | (v2_struct_0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [t23_tsep_1])).
% 0.19/0.51  thf('61', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_tsep_1 @ X1 @ X0 @ sk_B) != (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 0.19/0.51          | (v2_struct_0 @ X1)
% 0.19/0.51          | ~ (v2_pre_topc @ X1)
% 0.19/0.51          | ~ (l1_pre_topc @ X1)
% 0.19/0.51          | (v2_struct_0 @ sk_B)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.19/0.51          | (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.51          | (v2_struct_0 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_B)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.19/0.51        | (m1_pre_topc @ sk_B @ sk_B)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_B)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('eq_res', [status(thm)], ['61'])).
% 0.19/0.51  thf('63', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (m1_pre_topc @ sk_B @ sk_B)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.51  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (m1_pre_topc @ sk_B @ sk_B)
% 0.19/0.51        | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.19/0.51  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('69', plain, (((v2_struct_0 @ sk_B) | (m1_pre_topc @ sk_B @ sk_B))),
% 0.19/0.51      inference('clc', [status(thm)], ['67', '68'])).
% 0.19/0.51  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.19/0.51      inference('clc', [status(thm)], ['69', '70'])).
% 0.19/0.51  thf('72', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ sk_B)
% 0.19/0.51          | (v2_struct_0 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['49', '71'])).
% 0.19/0.51  thf('73', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_B)
% 0.19/0.51          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.51          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | (v2_struct_0 @ sk_C)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('simplify', [status(thm)], ['72'])).
% 0.19/0.51  thf('74', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_A)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.19/0.51         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51            (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['46', '73'])).
% 0.19/0.51  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('76', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_A)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51            (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('demod', [status(thm)], ['74', '75'])).
% 0.19/0.51  thf('77', plain,
% 0.19/0.51      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51           (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))))),
% 0.19/0.51      inference('split', [status(esa)], ['41'])).
% 0.19/0.51  thf('78', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_B)
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_A)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.19/0.51             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['76', '77'])).
% 0.19/0.51  thf('79', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('80', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_A)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (v2_struct_0 @ sk_B)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.19/0.51             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.19/0.51  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('82', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.19/0.51             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.19/0.51  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('84', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.19/0.51             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('clc', [status(thm)], ['82', '83'])).
% 0.19/0.51  thf('85', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('86', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_D))
% 0.19/0.51         <= (~
% 0.19/0.51             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.19/0.51             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.19/0.51      inference('clc', [status(thm)], ['84', '85'])).
% 0.19/0.51  thf('87', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('88', plain,
% 0.19/0.51      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51         (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.19/0.51       ~ ((m1_pre_topc @ sk_C @ sk_D))),
% 0.19/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.19/0.51  thf('89', plain,
% 0.19/0.51      (~
% 0.19/0.51       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51         (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['43', '45', '88'])).
% 0.19/0.51  thf('90', plain,
% 0.19/0.51      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51          (k2_tsep_1 @ sk_A @ sk_D @ sk_C))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['42', '89'])).
% 0.19/0.51  thf('91', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_A)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '90'])).
% 0.19/0.51  thf('92', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('93', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_B)
% 0.19/0.51         | (v2_struct_0 @ sk_D)
% 0.19/0.51         | (v2_struct_0 @ sk_C)
% 0.19/0.51         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.19/0.51  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('95', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.19/0.51         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.19/0.51  thf('96', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('97', plain,
% 0.19/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.19/0.51         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('clc', [status(thm)], ['95', '96'])).
% 0.19/0.51  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('99', plain, (((v2_struct_0 @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.19/0.51      inference('clc', [status(thm)], ['97', '98'])).
% 0.19/0.51  thf('100', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('101', plain, (~ ((m1_pre_topc @ sk_B @ sk_D))),
% 0.19/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.19/0.51  thf('102', plain,
% 0.19/0.51      (~
% 0.19/0.51       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.19/0.51         (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.19/0.51       ((m1_pre_topc @ sk_B @ sk_D))),
% 0.19/0.51      inference('split', [status(esa)], ['24'])).
% 0.19/0.51  thf('103', plain, ($false),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['1', '101', '102', '88'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
