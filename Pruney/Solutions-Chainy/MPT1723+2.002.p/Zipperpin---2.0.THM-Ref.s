%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wb4ut2clBn

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:32 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 238 expanded)
%              Number of leaves         :   14 (  68 expanded)
%              Depth                    :   26
%              Number of atoms          : 1047 (6482 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( m1_pre_topc @ X7 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X4 )
      | ( r1_tsep_1 @ X2 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X3 @ X2 @ X5 ) @ ( k2_tsep_1 @ X3 @ X4 @ X6 ) )
      | ~ ( m1_pre_topc @ X6 @ X3 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X3 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_tmap_1])).

thf('9',plain,(
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
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
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
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,
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
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['16','21','22'])).

thf('24',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['25'])).

thf('28',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i] :
      ( ( m1_pre_topc @ X7 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    inference('sup-',[status(thm)],['6','12'])).

thf('35',plain,(
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
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['30','44'])).

thf('46',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['25'])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['27','29','57'])).

thf('59',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['26','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['24','59'])).

thf('61',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','71','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wb4ut2clBn
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 184 iterations in 0.149s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.40/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.60  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.40/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(t32_tmap_1, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.60               ( ![D:$i]:
% 0.40/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.40/0.60                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.40/0.60                     ( ( ( m1_pre_topc @ B @ D ) =>
% 0.40/0.60                         ( m1_pre_topc @
% 0.40/0.60                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.40/0.60                           ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 0.40/0.60                       ( ( m1_pre_topc @ C @ D ) =>
% 0.40/0.60                         ( m1_pre_topc @
% 0.40/0.60                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.40/0.60                           ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.60            ( l1_pre_topc @ A ) ) =>
% 0.40/0.60          ( ![B:$i]:
% 0.40/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.60              ( ![C:$i]:
% 0.40/0.60                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.60                  ( ![D:$i]:
% 0.40/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.40/0.60                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.40/0.60                        ( ( ( m1_pre_topc @ B @ D ) =>
% 0.40/0.60                            ( m1_pre_topc @
% 0.40/0.60                              ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.40/0.60                              ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 0.40/0.60                          ( ( m1_pre_topc @ C @ D ) =>
% 0.40/0.60                            ( m1_pre_topc @
% 0.40/0.60                              ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.40/0.60                              ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t32_tmap_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (((m1_pre_topc @ sk_B @ sk_D) | (m1_pre_topc @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (((m1_pre_topc @ sk_C @ sk_D)) | ((m1_pre_topc @ sk_B @ sk_D))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf(t2_tsep_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X7 : $i]: ((m1_pre_topc @ X7 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (((m1_pre_topc @ sk_B @ sk_D)
% 0.40/0.60        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (((m1_pre_topc @ sk_B @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('split', [status(esa)], ['3'])).
% 0.40/0.60  thf('5', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t28_tmap_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.60               ( ![D:$i]:
% 0.40/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.40/0.60                   ( ![E:$i]:
% 0.40/0.60                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.40/0.60                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 0.40/0.60                         ( ( r1_tsep_1 @ B @ C ) | 
% 0.40/0.60                           ( m1_pre_topc @
% 0.40/0.60                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.40/0.60                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.60         ((v2_struct_0 @ X2)
% 0.40/0.60          | ~ (m1_pre_topc @ X2 @ X3)
% 0.40/0.60          | (v2_struct_0 @ X4)
% 0.40/0.60          | ~ (m1_pre_topc @ X4 @ X3)
% 0.40/0.60          | ~ (m1_pre_topc @ X2 @ X4)
% 0.40/0.60          | (r1_tsep_1 @ X2 @ X5)
% 0.40/0.60          | ~ (m1_pre_topc @ X5 @ X6)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ X3 @ X2 @ X5) @ 
% 0.40/0.60             (k2_tsep_1 @ X3 @ X4 @ X6))
% 0.40/0.60          | ~ (m1_pre_topc @ X6 @ X3)
% 0.40/0.60          | (v2_struct_0 @ X6)
% 0.40/0.60          | ~ (m1_pre_topc @ X5 @ X3)
% 0.40/0.60          | (v2_struct_0 @ X5)
% 0.40/0.60          | ~ (l1_pre_topc @ X3)
% 0.40/0.60          | ~ (v2_pre_topc @ X3)
% 0.40/0.60          | (v2_struct_0 @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [t28_tmap_1])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X1)
% 0.40/0.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ X1)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.40/0.60          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X2)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.60  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X1)
% 0.40/0.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ X1)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.40/0.60          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X2)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.40/0.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X1)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 0.40/0.60          | (v2_struct_0 @ sk_D)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      ((![X0 : $i]:
% 0.40/0.60          ((v2_struct_0 @ sk_B)
% 0.40/0.60           | (v2_struct_0 @ sk_D)
% 0.40/0.60           | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.40/0.60           | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60              (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.40/0.60           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60           | (v2_struct_0 @ X0)
% 0.40/0.60           | (v2_struct_0 @ sk_C)
% 0.40/0.60           | (v2_struct_0 @ sk_A)))
% 0.40/0.60         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (((~ (l1_pre_topc @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.40/0.60         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.40/0.60         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '15'])).
% 0.40/0.60  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(dt_m1_pre_topc, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.40/0.60  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.40/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('21', plain, ((l1_pre_topc @ sk_C)),
% 0.40/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.60  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_A)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.40/0.60         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('demod', [status(thm)], ['16', '21', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.40/0.60        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60           (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_D @ sk_C))))),
% 0.40/0.60      inference('split', [status(esa)], ['25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (~
% 0.40/0.60       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60         (k2_tsep_1 @ sk_A @ sk_D @ sk_C))) | 
% 0.40/0.60       ~
% 0.40/0.60       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60         (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.40/0.60      inference('split', [status(esa)], ['25'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.40/0.60        | (m1_pre_topc @ sk_C @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (((m1_pre_topc @ sk_C @ sk_D)) | 
% 0.40/0.60       ~
% 0.40/0.60       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60         (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 0.40/0.60      inference('split', [status(esa)], ['28'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (((m1_pre_topc @ sk_C @ sk_D)) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('split', [status(esa)], ['28'])).
% 0.40/0.60  thf('31', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X7 : $i]: ((m1_pre_topc @ X7 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.40/0.60  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.40/0.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X1)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '12'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_B)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (l1_pre_topc @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['32', '36'])).
% 0.40/0.60  thf('38', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.40/0.60  thf('40', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.60  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | (v2_struct_0 @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.40/0.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.40/0.60          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['37', '42'])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (((v2_struct_0 @ sk_B)
% 0.40/0.60        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.40/0.60        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60           (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.40/0.60        | (v2_struct_0 @ sk_D)
% 0.40/0.60        | (v2_struct_0 @ sk_C)
% 0.40/0.60        | (v2_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['31', '43'])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_A)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60            (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.40/0.60         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['30', '44'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60           (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))))),
% 0.40/0.60      inference('split', [status(esa)], ['25'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_B)
% 0.40/0.60         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_A)))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.40/0.60             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.60  thf('48', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_A)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (v2_struct_0 @ sk_B)))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.40/0.60             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.60  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.40/0.60             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.60  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.40/0.60             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('clc', [status(thm)], ['51', '52'])).
% 0.40/0.60  thf('54', plain, (~ (v2_struct_0 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      (((v2_struct_0 @ sk_D))
% 0.40/0.60         <= (~
% 0.40/0.60             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.40/0.60             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.40/0.60      inference('clc', [status(thm)], ['53', '54'])).
% 0.40/0.60  thf('56', plain, (~ (v2_struct_0 @ sk_D)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60         (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.40/0.60       ~ ((m1_pre_topc @ sk_C @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      (~
% 0.40/0.60       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60         (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['27', '29', '57'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60          (k2_tsep_1 @ sk_A @ sk_D @ sk_C))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['26', '58'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_A)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['24', '59'])).
% 0.40/0.60  thf('61', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_D)
% 0.40/0.60         | (v2_struct_0 @ sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.60  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.40/0.60         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.40/0.60  thf('65', plain, (~ (v2_struct_0 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.40/0.60         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('clc', [status(thm)], ['64', '65'])).
% 0.40/0.60  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('68', plain, (((v2_struct_0 @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.40/0.60      inference('clc', [status(thm)], ['66', '67'])).
% 0.40/0.60  thf('69', plain, (~ (v2_struct_0 @ sk_D)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('70', plain, (~ ((m1_pre_topc @ sk_B @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (~
% 0.40/0.60       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.60         (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.40/0.60       ((m1_pre_topc @ sk_B @ sk_D))),
% 0.40/0.60      inference('split', [status(esa)], ['3'])).
% 0.40/0.60  thf('72', plain, ($false),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['1', '70', '71', '57'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
